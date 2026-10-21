-- Prove2me | solution 1 for TractableDRO.MeanSupport.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-21T00:52:30.738095+00:00
-- url     : https://prove2.me/submissions/00ecab80-ceaf-4ff0-8cdf-1072b27eed72

import Mathlib
import Definitions.Def_TractableDRO_MeanSupport_Model

open MeasureTheory
open MeasureTheory Set Filter
open scoped BigOperators ENNReal

namespace MeanSupportProof

end MeanSupportProof

open MeasureTheory Set Filter
open scoped BigOperators ENNReal
open TractableDRO.MeanSupport

namespace MeanSupportProof
variable {n : ℕ}

def Supported (V : Set (Fin n → ℝ)) (P : Measure (Fin n → ℝ)) : Prop :=
  IsProbabilityMeasure P ∧ (∀ i, Integrable (fun x => x i) P) ∧ ∀ᵐ x ∂P, x ∈ V

lemma supported_dirac {V : Set (Fin n → ℝ)} {x : Fin n → ℝ} (hx : x ∈ V) :
    Supported V (Measure.dirac x) := by
  refine ⟨inferInstance, fun i => integrable_dirac (by simp), ?_⟩
  simpa using hx

lemma mean_dirac (x : Fin n → ℝ) : MomentDRO.Conf.meanVec (Measure.dirac x) = x := by
  funext i
  simp [MomentDRO.Conf.meanVec]

lemma expPos_dirac (x : Fin n → ℝ) (r0 : ℝ) (r : Fin n → ℝ) :
    expPos (Measure.dirac x) r0 r = max (r0 + r ⬝ᵥ x) 0 := by
  simp [expPos]

lemma expPos_nonneg (P : Measure (Fin n → ℝ)) (r0 : ℝ) (r : Fin n → ℝ) :
    0 ≤ expPos P r0 r := integral_nonneg (fun _ => le_max_right _ _)

lemma supported_linear {V : Set (Fin n → ℝ)} {P : Measure (Fin n → ℝ)}
    (hP : Supported V P) (s : Fin n → ℝ) : Integrable (fun x => s ⬝ᵥ x) P := by
  exact integrable_finsetSum _ (fun i _ => (hP.2.1 i).const_mul (s i))

lemma supported_loss {V : Set (Fin n → ℝ)} {P : Measure (Fin n → ℝ)}
    (hP : Supported V P) (r0 : ℝ) (r : Fin n → ℝ) :
    Integrable (fun x => max (r0 + r ⬝ᵥ x) 0) P := by
  let : IsProbabilityMeasure P := hP.1
  exact ((integrable_const r0).add (supported_linear hP r)).pos_part

lemma integral_linear {V : Set (Fin n → ℝ)} {P : Measure (Fin n → ℝ)}
    (hP : Supported V P) (s : Fin n → ℝ) :
    (∫ x, s ⬝ᵥ x ∂P) = s ⬝ᵥ MomentDRO.Conf.meanVec P := by
  simp only [dotProduct, MomentDRO.Conf.meanVec]
  rw [integral_finsetSum _ (fun i _ => (hP.2.1 i).const_mul (s i))]
  simp only [integral_const_mul]

noncomputable def mix (a b : ℝ) (P Q : Measure (Fin n → ℝ)) : Measure (Fin n → ℝ) :=
  ENNReal.ofReal a • P + ENNReal.ofReal b • Q

lemma supported_mix {V : Set (Fin n → ℝ)} {P Q : Measure (Fin n → ℝ)}
    (hP : Supported V P) (hQ : Supported V Q) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) : Supported V (mix a b P Q) := by
  let : IsProbabilityMeasure P := hP.1
  let : IsProbabilityMeasure Q := hQ.1
  refine ⟨⟨?_⟩, fun i => ?_, ?_⟩
  · simp only [mix, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_add ha hb, hab, ENNReal.ofReal_one]
  · exact (hP.2.1 i).smul_measure ENNReal.ofReal_ne_top |>.add_measure
      ((hQ.2.1 i).smul_measure ENNReal.ofReal_ne_top)
  · exact ae_add_measure_iff.mpr ⟨Measure.ae_smul_measure hP.2.2 _, Measure.ae_smul_measure hQ.2.2 _⟩

lemma mean_mix {V : Set (Fin n → ℝ)} {P Q : Measure (Fin n → ℝ)}
    (hP : Supported V P) (hQ : Supported V Q) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    MomentDRO.Conf.meanVec (mix a b P Q) =
      a • MomentDRO.Conf.meanVec P + b • MomentDRO.Conf.meanVec Q := by
  funext i
  rw [MomentDRO.Conf.meanVec, mix, integral_add_measure
    ((hP.2.1 i).smul_measure ENNReal.ofReal_ne_top)
    ((hQ.2.1 i).smul_measure ENNReal.ofReal_ne_top)]
  simp [MomentDRO.Conf.meanVec, ENNReal.toReal_ofReal ha, ENNReal.toReal_ofReal hb]

lemma expPos_mix {V : Set (Fin n → ℝ)} {P Q : Measure (Fin n → ℝ)}
    (hP : Supported V P) (hQ : Supported V Q) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (r0 : ℝ) (r : Fin n → ℝ) :
    expPos (mix a b P Q) r0 r = a * expPos P r0 r + b * expPos Q r0 r := by
  rw [expPos, mix, integral_add_measure
    ((supported_loss hP r0 r).smul_measure ENNReal.ofReal_ne_top)
    ((supported_loss hQ r0 r).smul_measure ENNReal.ofReal_ne_top)]
  simp [expPos, ENNReal.toReal_ofReal ha, ENNReal.toReal_ofReal hb]

lemma primal_nonneg {V Vhat : Set (Fin n → ℝ)}
    (hCQ : (Vhat ∩ interior V).Nonempty) (r0 : ℝ) (r : Fin n → ℝ) :
    (0 : EReal) ≤ worstCase (family1 V Vhat) r0 r := by
  obtain ⟨x, hx, hv⟩ := hCQ
  have hp := supported_dirac (interior_subset hv)
  have hf : Measure.dirac x ∈ family1 V Vhat :=
    ⟨hp.1, hp.2.1, by simpa [mean_dirac] using hx, hp.2.2⟩
  exact le_trans (by exact_mod_cast expPos_nonneg (Measure.dirac x) r0 r)
    (le_iSup_of_le (Measure.dirac x) (le_iSup_of_le hf le_rfl))

end MeanSupportProof

open MeasureTheory Set Filter
open scoped BigOperators ENNReal
open TractableDRO.MeanSupport

namespace MeanSupportProof
variable {n : ℕ}

lemma payoff_sub (r0 : ℝ) (r s x : Fin n → ℝ) :
    max (r0 + r ⬝ᵥ x - s ⬝ᵥ x) (-(s ⬝ᵥ x)) = max (r0 + r ⬝ᵥ x) 0 - s ⬝ᵥ x := by
  simpa only [zero_sub] using (max_sub_sub_right (r0 + r ⬝ᵥ x) 0 (s ⬝ᵥ x))

lemma weak_at {V Vhat : Set (Fin n → ℝ)} (hV : V.Nonempty) (hVh : Vhat.Nonempty)
    (r0 : ℝ) (r s : Fin n → ℝ) {P : Measure (Fin n → ℝ)}
    (hP : P ∈ family1 V Vhat) : (expPos P r0 r : EReal) ≤ pi1Obj V Vhat r0 r s := by
  let A : EReal := ⨆ z ∈ Vhat, ((s ⬝ᵥ z : ℝ) : EReal)
  let B : EReal := ⨆ x ∈ V, ((max (r0+r ⬝ᵥ x-s ⬝ᵥ x) (-(s ⬝ᵥ x)) : ℝ) : EReal)
  have ha (z) (hz : z ∈ Vhat) : ((s ⬝ᵥ z : ℝ) : EReal) ≤ A :=
    le_iSup_of_le z (le_iSup_of_le hz le_rfl)
  have hb (x) (hx : x ∈ V) :
      ((max (r0+r ⬝ᵥ x-s ⬝ᵥ x) (-(s ⬝ᵥ x)) : ℝ) : EReal) ≤ B :=
    le_iSup_of_le x (le_iSup_of_le hx le_rfl)
  have hAb : A ≠ ⊥ := by
    obtain ⟨z,hz⟩ := hVh
    exact ne_of_gt (lt_of_lt_of_le (EReal.bot_lt_coe _) (ha z hz))
  have hBb : B ≠ ⊥ := by
    obtain ⟨x,hx⟩ := hV
    exact ne_of_gt (lt_of_lt_of_le (EReal.bot_lt_coe _) (hb x hx))
  change (expPos P r0 r : EReal) ≤ A + B
  by_cases hAt : A = ⊤
  · rw [hAt, EReal.top_add_of_ne_bot hBb]
    exact le_top
  by_cases hBt : B = ⊤
  · rw [hBt, EReal.add_top_of_ne_bot hAb]
    exact le_top
  have hAe := EReal.coe_toReal hAt hAb
  have hBe := EReal.coe_toReal hBt hBb
  have hsup : Supported V P := ⟨hP.1,hP.2.1,hP.2.2.2⟩
  let : IsProbabilityMeasure P := hP.1
  have hmean : s ⬝ᵥ MomentDRO.Conf.meanVec P ≤ A.toReal := by
    exact EReal.coe_le_coe_iff.mp (by rw [hAe]; exact ha _ hP.2.2.1)
  have hpoint : ∀ᵐ x ∂P, max (r0+r ⬝ᵥ x) 0 - s ⬝ᵥ x ≤ B.toReal := by
    filter_upwards [hP.2.2.2] with x hx
    apply EReal.coe_le_coe_iff.mp
    rw [hBe, ← payoff_sub]
    exact hb x hx
  have hi := integral_mono_ae ((supported_loss hsup r0 r).sub (supported_linear hsup s))
    (integrable_const B.toReal) hpoint
  change (∫ x, max (r0+r ⬝ᵥ x) 0 - s ⬝ᵥ x ∂P) ≤ (∫ x, B.toReal ∂P) at hi
  rw [integral_sub (supported_loss hsup r0 r) (supported_linear hsup s),
    integral_linear hsup s] at hi
  simp only [integral_const, probReal_univ, one_smul] at hi
  have hreal : expPos P r0 r ≤ A.toReal + B.toReal := by
    change expPos P r0 r - s ⬝ᵥ MomentDRO.Conf.meanVec P ≤ B.toReal at hi
    linarith
  rw [← hAe, ← hBe, ← EReal.coe_add]
  exact_mod_cast hreal

lemma weak_duality {V Vhat : Set (Fin n → ℝ)}
    (hCQ : (Vhat ∩ interior V).Nonempty) (r0 : ℝ) (r : Fin n → ℝ) :
    worstCase (family1 V Vhat) r0 r ≤ pi1 V Vhat r0 r := by
  obtain ⟨x,hx,hv⟩ := hCQ
  apply le_iInf
  intro s
  apply iSup_le
  intro P
  apply iSup_le
  intro hP
  exact weak_at ⟨x,interior_subset hv⟩ ⟨x,hx⟩ r0 r s hP

lemma dual_le_of_joint {V Vhat : Set (Fin n → ℝ)} (hV : V.Nonempty) (hVh : Vhat.Nonempty)
    (r0 : ℝ) (r s : Fin n → ℝ) (q : ℝ)
    (hj : ∀ x ∈ V, ∀ z ∈ Vhat, s ⬝ᵥ z + max (r0+r ⬝ᵥ x) 0 - s ⬝ᵥ x ≤ q) :
    pi1 V Vhat r0 r ≤ (q : EReal) := by
  let S : Set ℝ := (fun z => s ⬝ᵥ z) '' Vhat
  have hSne : S.Nonempty := hVh.image _
  have hSb : BddAbove S := by
    obtain ⟨x,hx⟩ := hV
    refine ⟨q - max (r0+r ⬝ᵥ x) 0 + s ⬝ᵥ x, ?_⟩
    rintro _ ⟨z,hz,rfl⟩
    have h := hj x hx z hz
    linarith
  let a : ℝ := sSup S
  have hfirst : (⨆ z ∈ Vhat, ((s ⬝ᵥ z : ℝ) : EReal)) ≤ (a : EReal) := by
    apply iSup_le
    intro z
    apply iSup_le
    intro hz
    exact_mod_cast (le_csSup hSb (show s ⬝ᵥ z ∈ S from ⟨z,hz,rfl⟩))
  have hsecond : (⨆ x ∈ V,
      ((max (r0+r ⬝ᵥ x-s ⬝ᵥ x) (-(s ⬝ᵥ x)) : ℝ) : EReal)) ≤ ((q-a : ℝ) : EReal) := by
    apply iSup_le
    intro x
    apply iSup_le
    intro hx
    have ha : a ≤ q - max (r0+r ⬝ᵥ x) 0 + s ⬝ᵥ x := by
      apply csSup_le hSne
      rintro _ ⟨z,hz,rfl⟩
      have h := hj x hx z hz
      linarith
    rw [payoff_sub]
    exact_mod_cast (show max (r0+r ⬝ᵥ x) 0 - s ⬝ᵥ x ≤ q-a by linarith)
  apply le_trans (iInf_le (fun t => pi1Obj V Vhat r0 r t) s)
  change _ + _ ≤ (q : EReal)
  calc
    _ ≤ (a : EReal) + ((q-a : ℝ) : EReal) := add_le_add hfirst hsecond
    _ = (q : EReal) := by rw [← EReal.coe_add]; congr 1; ring

end MeanSupportProof

noncomputable section
open Set Matrix
open scoped BigOperators Topology Classical
namespace MeanSupportProof

variable {n : ℕ}
local notation "E" => Fin n → ℝ

theorem vertical_certificate {C : Set (E × ℝ)} {q : ℝ}
    (hC : Convex ℝ C) (hbase : ((0, -1) : E × ℝ) ∈ interior C)
    (hq : 0 ≤ q) (hout : ((0, q) : E × ℝ) ∉ C) :
    ∃ s : E, ∀ p ∈ C, p.2 - s ⬝ᵥ p.1 ≤ q := by
  obtain ⟨ell, hell⟩ := geometric_hahn_banach_open_point hC.interior isOpen_interior
    (show ((0, q) : E × ℝ) ∉ interior C from fun h => hout (interior_subset h))
  have hext : C ⊆ {p | ell p ≤ ell (0, q)} := by
    have hi : interior C ⊆ {p | ell p ≤ ell (0, q)} := fun p hp => (hell p hp).le
    have hc := closure_minimal hi (isClosed_le ell.continuous continuous_const)
    rw [hC.closure_interior_eq_closure_of_nonempty_interior ⟨_, hbase⟩] at hc
    exact subset_trans subset_closure hc
  let u : StrongDual ℝ E := ell.comp (ContinuousLinearMap.inl ℝ E ℝ)
  let b : ℝ := ell (0, 1)
  have split (d : E) (t : ℝ) : ell (d, t) = u d + b * t := by
    have he : (d, t) = (d, (0 : ℝ)) + t • ((0 : E), (1 : ℝ)) := by ext <;> simp
    rw [he, map_add, map_smul]
    simp [u, b, mul_comm]
  have hb : 0 < b := by
    have hh := hell (0, -1) hbase
    rw [split, split, map_zero] at hh
    by_contra hn
    have hn' : b ≤ 0 := le_of_not_gt hn
    have hm : b * q ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hn' hq
    linarith
  have hu (d : E) : u d = ∑ i, d i * u (Pi.single i 1) := by
    conv_lhs => rw [pi_eq_sum_univ' d]
    simp only [map_sum, map_smul, smul_eq_mul]
  let s : E := fun i => -u (Pi.single i 1) / b
  have hs (d : E) : b * (s ⬝ᵥ d) = -u d := by
    rw [hu, ← Finset.sum_neg_distrib]
    simp only [dotProduct, Finset.mul_sum, s]
    apply Finset.sum_congr rfl
    intro i _
    field_simp
  refine ⟨s, ?_⟩
  rintro ⟨d, t⟩ hp
  have hh := hext hp
  change ell (d, t) ≤ ell (0, q) at hh
  rw [split, split, map_zero] at hh
  have hd := hs d
  apply (mul_le_mul_iff_right₀ hb).mp
  nlinarith

end MeanSupportProof

noncomputable section
open MeasureTheory Set Filter Matrix
open scoped BigOperators ENNReal Topology Classical
open TractableDRO.MeanSupport
namespace MeanSupportProof

variable {n : ℕ}
local notation "E" => Fin n → ℝ

def achievable (V Vhat : Set E) (r0 : ℝ) (r : E) : Set (E × ℝ) :=
  {p | ∃ (P : Measure E) (z : E), Supported V P ∧ z ∈ Vhat ∧
    p.1 = MomentDRO.Conf.meanVec P - z ∧ p.2 < expPos P r0 r}

theorem achievable_convex {V Vhat : Set E} (hv : Convex ℝ Vhat) (r0 : ℝ) (r : E) :
    Convex ℝ (achievable V Vhat r0 r) := by
  rintro p ⟨P, z, hP, hz, hp, ht⟩ q ⟨Q, w, hQ, hw, hq, hu⟩ a b ha hb hab
  refine ⟨mix a b P Q, a • z + b • w, supported_mix hP hQ ha hb hab,
    hv hz hw ha hb hab, ?_, ?_⟩
  · change a • p.1 + b • q.1 = _
    rw [hp, hq, mean_mix hP hQ ha hb]
    module
  · change a * p.2 + b * q.2 < _
    rw [expPos_mix hP hQ ha hb]
    have habp : 0 < a ∨ 0 < b := by
      by_contra hn
      push Not at hn
      linarith
    rcases habp with ha' | hb'
    · exact add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left ht ha')
        (mul_le_mul_of_nonneg_left hu.le hb)
    · exact add_lt_add_of_le_of_lt (mul_le_mul_of_nonneg_left ht.le ha)
        (mul_lt_mul_of_pos_left hu hb')

theorem achievable_dirac {V Vhat : Set E} {x z : E} (hx : x ∈ V) (hz : z ∈ Vhat)
    (r0 : ℝ) (r : E) {t : ℝ} (ht : t < max (r0 + r ⬝ᵥ x) 0) :
    (x - z, t) ∈ achievable V Vhat r0 r := by
  exact ⟨Measure.dirac x, z, supported_dirac hx, hz, by rw [mean_dirac],
    by simpa only [expPos_dirac] using ht⟩

theorem achievable_interior {V Vhat : Set E}
    (hCQ : (Vhat ∩ interior V).Nonempty) (r0 : ℝ) (r : E) :
    ((0, -1) : E × ℝ) ∈ interior (achievable V Vhat r0 r) := by
  obtain ⟨z, hz, hv⟩ := hCQ
  let U : Set (E × ℝ) := {p | z + p.1 ∈ interior V ∧ p.2 < 0}
  have ho : IsOpen U :=
    (isOpen_interior.preimage (continuous_const.add continuous_fst)).inter
      (isOpen_lt continuous_snd continuous_const)
  have hbase : ((0, -1) : E × ℝ) ∈ U := by simpa [U] using hv
  have hsub : U ⊆ achievable V Vhat r0 r := by
    rintro ⟨d, t⟩ ⟨hd, ht⟩
    have hh := achievable_dirac (interior_subset hd) hz r0 r
      (ht.trans_le (le_max_right _ _))
    simpa only [add_sub_cancel_left] using hh
  exact mem_interior_iff_mem_nhds.mpr (mem_of_superset (ho.mem_nhds hbase) hsub)

theorem achievable_excludes {V Vhat : Set E} {r0 : ℝ} {r : E} {q : ℝ}
    (hq : worstCase (family1 V Vhat) r0 r < (q : EReal)) :
    ((0, q) : E × ℝ) ∉ achievable V Vhat r0 r := by
  rintro ⟨P, z, hP, hz, he, ht⟩
  have hm : MomentDRO.Conf.meanVec P = z := sub_eq_zero.mp he.symm
  have hf : P ∈ family1 V Vhat := ⟨hP.1, hP.2.1, by simpa only [hm] using hz, hP.2.2⟩
  have hb : (expPos P r0 r : EReal) ≤ worstCase (family1 V Vhat) r0 r :=
    le_iSup_of_le P (le_iSup_of_le hf le_rfl)
  have hh : (q : EReal) < expPos P r0 r := by exact_mod_cast ht
  exact (lt_irrefl (q : EReal)) (hh.trans_le hb |>.trans hq)

end MeanSupportProof

noncomputable section
open MeasureTheory Set Matrix
open scoped BigOperators ENNReal Topology Classical
open TractableDRO.MeanSupport
namespace MeanSupportProof

variable {n : ℕ}

theorem joint_certificate {V Vhat : Set (Fin n → ℝ)}
    (hv : Convex ℝ Vhat) (hCQ : (Vhat ∩ interior V).Nonempty)
    (r0 : ℝ) (r : Fin n → ℝ) {q : ℝ}
    (hq : worstCase (family1 V Vhat) r0 r < (q : EReal)) :
    ∃ s : Fin n → ℝ, ∀ x ∈ V, ∀ z ∈ Vhat,
      s ⬝ᵥ z + max (r0 + r ⬝ᵥ x) 0 - s ⬝ᵥ x ≤ q := by
  have hqp : 0 ≤ q := by
    have hh := (primal_nonneg hCQ r0 r).trans hq.le
    exact_mod_cast hh
  obtain ⟨s, hs⟩ := vertical_certificate (achievable_convex hv r0 r)
    (achievable_interior hCQ r0 r) hqp (achievable_excludes hq)
  refine ⟨s, ?_⟩
  intro x hx z hz
  apply le_of_forall_pos_le_add
  intro ε hε
  have ht : max (r0 + r ⬝ᵥ x) 0 - ε < max (r0 + r ⬝ᵥ x) 0 := sub_lt_self _ hε
  have hh := hs (x-z, max (r0 + r ⬝ᵥ x) 0 - ε) (achievable_dirac hx hz r0 r ht)
  change max (r0 + r ⬝ᵥ x) 0 - ε - s ⬝ᵥ (x-z) ≤ q at hh
  rw [dotProduct_sub] at hh
  linarith

end MeanSupportProof

open MeasureTheory Set

namespace TractableDRO.MeanSupport

theorem theorem_1 {n : ℕ} (V Vhat : Set (Fin n → ℝ))
    (hVconv : Convex ℝ V) (hVclosed : IsClosed V)
    (hVhconv : Convex ℝ Vhat) (hVhclosed : IsClosed Vhat)
    (hCQ : (Vhat ∩ interior V).Nonempty) (r0 : ℝ) (r : Fin n → ℝ) :
    worstCase (family1 V Vhat) r0 r = pi1 V Vhat r0 r := by
  have _ := hVconv
  have _ := hVclosed
  have _ := hVhclosed
  apply le_antisymm (MeanSupportProof.weak_duality hCQ r0 r)
  by_contra hn
  have hlt := lt_of_not_ge hn
  obtain ⟨q, hq, hqd⟩ := EReal.lt_iff_exists_real_btwn.mp hlt
  obtain ⟨s, hs⟩ := MeanSupportProof.joint_certificate hVhconv hCQ r0 r hq
  obtain ⟨x, hx, hv⟩ := hCQ
  have hd := MeanSupportProof.dual_le_of_joint ⟨x, interior_subset hv⟩ ⟨x, hx⟩ r0 r s q hs
  exact (not_lt_of_ge hd) hqd

end TractableDRO.MeanSupport

open TractableDRO.MeanSupport
theorem solution {n : ℕ} (V Vhat : Set (Fin n → ℝ))
    (hVconv : Convex ℝ V) (hVclosed : IsClosed V)
    (hVhconv : Convex ℝ Vhat) (hVhclosed : IsClosed Vhat)
    (hCQ : (Vhat ∩ interior V).Nonempty) (r0 : ℝ) (r : Fin n → ℝ) :
    worstCase (family1 V Vhat) r0 r = pi1 V Vhat r0 r :=
  TractableDRO.MeanSupport.theorem_1 V Vhat hVconv hVclosed hVhconv hVhclosed hCQ r0 r
