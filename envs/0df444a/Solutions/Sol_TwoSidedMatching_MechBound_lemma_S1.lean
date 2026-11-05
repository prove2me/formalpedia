-- Prove2me | solution 1 for TwoSidedMatching.MechBound.lemma_S1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T21:12:49.988829+00:00
-- url     : https://prove2.me/submissions/768d4d23-63bb-4b99-853e-12820ac02d04

import Mathlib
import Definitions.Def_TwoSidedMatching_MechBound_Mechanism

open MeasureTheory MechanismDesign.BilateralTrade

namespace TwoSidedMatching.Guarantee.S1Copy

lemma timeLaw_prob (T : ℝ) (hT : 0 < T) : IsProbabilityMeasure (timeLaw T) := by
  refine ⟨?_⟩
  unfold timeLaw
  rw [Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
    Real.volume_Icc, smul_eq_mul, ← ENNReal.ofReal_mul (by positivity)]
  have : 1 / T * (T - 0) = 1 := by rw [sub_zero]; field_simp
  rw [this]; simp

open MechanismDesign.BilateralTrade in
lemma valLaw_prob (E : Environment) : IsProbabilityMeasure (valLaw E) := by
  refine ⟨?_⟩
  unfold valLaw
  have hI : IntegrableOn E.fB (Set.Icc E.loB E.hiB) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le E.loB_lt_hiB.le).1 E.fB_intervalIntegrable
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Icc E.loB E.hiB)] E.fB :=
    (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall (fun x hx => (E.fB_pos x hx).le))
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hI hnn]
  have : ∫ x in Set.Icc E.loB E.hiB, E.fB x = 1 := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le E.loB_lt_hiB.le]
    exact E.fB_integral
  rw [this]; simp

open MechanismDesign.BilateralTrade in
lemma costLaw_prob (E : Environment) : IsProbabilityMeasure (costLaw E) := by
  refine ⟨?_⟩
  unfold costLaw
  have hI : IntegrableOn E.fS (Set.Icc E.loS E.hiS) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le E.loS_lt_hiS.le).1 E.fS_intervalIntegrable
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Icc E.loS E.hiS)] E.fS :=
    (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall (fun x hx => (E.fS_pos x hx).le))
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hI hnn]
  have : ∫ x in Set.Icc E.loS E.hiS, E.fS x = 1 := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le E.loS_lt_hiS.le]
    exact E.fS_integral
  rw [this]; simp

lemma sideLaw_prob (r T : ℝ) (Q : Measure (ℝ × ℝ)) [IsProbabilityMeasure Q] :
    IsProbabilityMeasure (sideLaw r T Q) := by
  unfold sideLaw
  have h1 : IsProbabilityMeasure (Measure.infinitePi (fun _ : ℕ => Q)) := inferInstance
  have h2' : ∀ ρ : NNReal, IsProbabilityMeasure (ProbabilityTheory.poissonMeasure ρ) :=
    fun ρ => inferInstance
  have h2 := h2' ⟨max (r * T) 0, le_max_right _ _⟩
  infer_instance

end TwoSidedMatching.Guarantee.S1Copy

namespace TwoSidedMatching.MechBound.S1Aux

open TwoSidedMatching.MechBound

lemma ae_mark (μ ν : Measure ℝ) [SFinite μ] [SFinite ν] (A B : Set ℝ)
    (hA : ∀ᵐ x ∂μ, x ∈ A) (hB : ∀ᵐ x ∂ν, x ∈ B) :
    ∀ᵐ z ∂(μ.prod ν), z ∈ A ×ˢ B := by
  have h1 := (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := ν)).ae hA
  have h2 := (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := ν)).ae hB
  filter_upwards [h1, h2] with z hz1 hz2
  exact ⟨hz1, hz2⟩

lemma ae_time (T : ℝ) : ∀ᵐ x ∂(TwoSidedMatching.Guarantee.timeLaw T), x ∈ Set.Icc 0 T := by
  unfold TwoSidedMatching.Guarantee.timeLaw
  exact (Measure.ae_smul_measure (ae_restrict_mem measurableSet_Icc) _)

lemma ae_dens (lo hi : ℝ) (f : ℝ → ℝ) :
    ∀ᵐ x ∂((volume.restrict (Set.Icc lo hi)).withDensity (fun v => ENNReal.ofReal (f v))),
      x ∈ Set.Icc lo hi :=
  (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Icc)

lemma ae_side (r T : ℝ) (Q : Measure (ℝ × ℝ)) [IsProbabilityMeasure Q] (A : Set (ℝ × ℝ))
    (hA : ∀ᵐ z ∂Q, z ∈ A) :
    ∀ᵐ x ∂(TwoSidedMatching.Guarantee.sideLaw r T Q), ∀ i, x.2 i ∈ A := by
  unfold TwoSidedMatching.Guarantee.sideLaw
  have hinf : ∀ᵐ w ∂(Measure.infinitePi (fun _ : ℕ => Q)), ∀ i, w i ∈ A := by
    rw [ae_all_iff]
    intro i
    exact (measurePreserving_eval_infinitePi (fun _ : ℕ => Q) i).quasiMeasurePreserving.ae hA
  exact (Measure.quasiMeasurePreserving_snd
    (μ := ProbabilityTheory.poissonMeasure ⟨max (r * T) 0, le_max_right _ _⟩)
    (ν := Measure.infinitePi (fun _ : ℕ => Q))).ae hinf

lemma ae_types (E : Environment) (lamD lamS T : ℝ) (hT : 0 < T) :
    ∀ᵐ ω ∂(P E lamD lamS T), (∀ φ ∈ Hd ω, φ ∈ buyerTypes E T) ∧ (∀ ψ ∈ Hs ω, ψ ∈ sellerTypes E T) := by
  have := TwoSidedMatching.Guarantee.S1Copy.timeLaw_prob T hT
  have hv : IsProbabilityMeasure (valLaw E) := TwoSidedMatching.Guarantee.S1Copy.valLaw_prob E
  have hc : IsProbabilityMeasure (costLaw E) := TwoSidedMatching.Guarantee.S1Copy.costLaw_prob E
  have hbm : IsProbabilityMeasure (buyerMark E T) := by
    unfold buyerMark; infer_instance
  have hsm : IsProbabilityMeasure (sellerMark E T) := by
    unfold sellerMark; infer_instance
  have hA : IsProbabilityMeasure (TwoSidedMatching.Guarantee.sideLaw lamD T (buyerMark E T)) :=
    TwoSidedMatching.Guarantee.S1Copy.sideLaw_prob _ _ _
  have hB : IsProbabilityMeasure (TwoSidedMatching.Guarantee.sideLaw lamS T (sellerMark E T)) :=
    TwoSidedMatching.Guarantee.S1Copy.sideLaw_prob _ _ _
  have hbt : ∀ᵐ z ∂(buyerMark E T), z ∈ buyerTypes E T :=
    ae_mark _ _ _ _ (ae_time T) (ae_dens _ _ _)
  have hst : ∀ᵐ z ∂(sellerMark E T), z ∈ sellerTypes E T :=
    ae_mark _ _ _ _ (ae_time T) (ae_dens _ _ _)
  have h1 := ae_side lamD T (buyerMark E T) _ hbt
  have h2 := ae_side lamS T (sellerMark E T) _ hst
  have g1 := (Measure.quasiMeasurePreserving_fst
    (μ := TwoSidedMatching.Guarantee.sideLaw lamD T (buyerMark E T))
    (ν := TwoSidedMatching.Guarantee.sideLaw lamS T (sellerMark E T))).ae h1
  have g2 := (Measure.quasiMeasurePreserving_snd
    (μ := TwoSidedMatching.Guarantee.sideLaw lamD T (buyerMark E T))
    (ν := TwoSidedMatching.Guarantee.sideLaw lamS T (sellerMark E T))).ae h2
  unfold P
  filter_upwards [g1, g2] with ω hω1 hω2
  refine ⟨fun φ hφ => ?_, fun ψ hψ => ?_⟩
  · simp only [Hd, Multiset.mem_map] at hφ
    obtain ⟨i, -, rfl⟩ := hφ
    exact hω1 i
  · simp only [Hs, Multiset.mem_map] at hψ
    obtain ⟨i, -, rfl⟩ := hψ
    exact hω2 i

lemma P_prob (E : Environment) (lamD lamS T : ℝ) (hT : 0 < T) :
    IsProbabilityMeasure (P E lamD lamS T) := by
  have := TwoSidedMatching.Guarantee.S1Copy.timeLaw_prob T hT
  have hv : IsProbabilityMeasure (valLaw E) := TwoSidedMatching.Guarantee.S1Copy.valLaw_prob E
  have hc : IsProbabilityMeasure (costLaw E) := TwoSidedMatching.Guarantee.S1Copy.costLaw_prob E
  have hbm : IsProbabilityMeasure (buyerMark E T) := by
    unfold buyerMark; infer_instance
  have hsm : IsProbabilityMeasure (sellerMark E T) := by
    unfold sellerMark; infer_instance
  have hA : IsProbabilityMeasure (TwoSidedMatching.Guarantee.sideLaw lamD T (buyerMark E T)) :=
    TwoSidedMatching.Guarantee.S1Copy.sideLaw_prob _ _ _
  have hB : IsProbabilityMeasure (TwoSidedMatching.Guarantee.sideLaw lamS T (sellerMark E T)) :=
    TwoSidedMatching.Guarantee.S1Copy.sideLaw_prob _ _ _
  unfold P
  infer_instance

lemma ins_eq (z1 : ℕ → ℝ × ℝ) (n : ℕ) (φhat : ℝ × ℝ) :
    (Multiset.range (n + 1)).map (Function.update z1 n φhat) =
      φhat ::ₘ (Multiset.range n).map z1 := by
  rw [Multiset.range_succ, Multiset.map_cons, Function.update_self]
  congr 1
  apply Multiset.map_congr rfl
  intro i hi
  rw [Function.update_of_ne (Nat.ne_of_lt (Multiset.mem_range.1 hi))]

lemma inserted_measurable (E : Environment) (lamD lamS T : ℝ) (y : Mechanism)
    (hwd : WellDefined E lamD lamS T y) (φhat : ℝ × ℝ) :
    Measurable (fun ω : TwoSidedMatching.Guarantee.Ω =>
      ((y (φhat ::ₘ Hd ω) (Hs ω)).1 φhat).toTriple) := by
  classical
  have hG : Measurable (fun p : (ℕ × ℕ) × ((ℕ → ℝ × ℝ) × (ℕ → ℝ × ℝ)) =>
      ((y (φhat ::ₘ (Multiset.range p.1.1).map p.2.1)
        ((Multiset.range p.1.2).map p.2.2)).1 φhat).toTriple) := by
    apply measurable_from_prod_countable_right
    intro nk
    obtain ⟨n, k⟩ := nk
    have h1 := hwd.buyer_measurable (n + 1) k n (Nat.lt_succ_self n)
    have h2 : Measurable (fun z : (ℕ → ℝ × ℝ) × (ℕ → ℝ × ℝ) =>
        (Function.update z.1 n φhat, z.2)) :=
      (measurable_update_left.comp measurable_fst).prodMk measurable_snd
    have h3 := h1.comp h2
    convert h3 using 1
    funext z
    simp only [Function.comp_apply, ins_eq, Function.update_self]
  have hpre : Measurable (fun ω : TwoSidedMatching.Guarantee.Ω =>
      ((ω.1.1, ω.2.1), (ω.1.2, ω.2.2))) := by fun_prop
  exact hG.comp hpre

lemma outcome_ae (E : Environment) (lamD lamS T : ℝ) (hT : 0 < T) (y : Mechanism)
    (hfeas : Feasible E T y) (φhat : ℝ × ℝ) (hφ : φhat ∈ buyerTypes E T) :
    ∀ᵐ ω ∂(P E lamD lamS T), AgentFeasible T φhat ((y (φhat ::ₘ Hd ω) (Hs ω)).1 φhat) := by
  filter_upwards [ae_types E lamD lamS T hT] with ω hω
  refine (hfeas (φhat ::ₘ Hd ω) (Hs ω) ?_ hω.2).1 φhat (Multiset.mem_cons_self _ _)
  intro x hx
  rw [Multiset.mem_cons] at hx
  rcases hx with rfl | hx
  · exact hφ
  · exact hω.1 x hx

lemma comp_integrable (E : Environment) (lamD lamS T : ℝ) (hT : 0 < T) (y : Mechanism)
    (hfeas : Feasible E T y) (hwd : WellDefined E lamD lamS T y)
    (φhat : ℝ × ℝ) (hφ : φhat ∈ buyerTypes E T) :
    Integrable (fun ω => ((y (φhat ::ₘ Hd ω) (Hs ω)).1 φhat).m) (P E lamD lamS T) ∧
    Integrable (fun ω => ((y (φhat ::ₘ Hd ω) (Hs ω)).1 φhat).s) (P E lamD lamS T) ∧
    Integrable (fun ω => ((y (φhat ::ₘ Hd ω) (Hs ω)).1 φhat).p) (P E lamD lamS T) := by
  have := P_prob E lamD lamS T hT
  have hm := inserted_measurable E lamD lamS T y hwd φhat
  have hae := outcome_ae E lamD lamS T hT y hfeas φhat hφ
  refine ⟨?_, ?_, hwd.buyer_interim_integrable φhat hφ⟩
  · refine Integrable.of_bound hm.snd.fst.aestronglyMeasurable 1 ?_
    filter_upwards [hae] with ω hω
    rcases hω.2.2 with h0 | h1
    · show ‖((y (φhat ::ₘ Hd ω) (Hs ω)).1 φhat).m‖ ≤ 1
      rw [h0]; simp
    · show ‖((y (φhat ::ₘ Hd ω) (Hs ω)).1 φhat).m‖ ≤ 1
      rw [h1]; simp
  · refine Integrable.of_bound hm.fst.aestronglyMeasurable (|φhat.1| + |T|) ?_
    filter_upwards [hae] with ω hω
    show ‖((y (φhat ::ₘ Hd ω) (Hs ω)).1 φhat).s‖ ≤ |φhat.1| + |T|
    rw [Real.norm_eq_abs, abs_le]
    obtain ⟨h1, h2, -⟩ := hω
    constructor
    · have := neg_abs_le φhat.1; have := abs_nonneg T; linarith
    · have := le_abs_self T; have := abs_nonneg φhat.1; linarith

lemma Eminus_Ud (E : Environment) (lamD lamS T b : ℝ) (hT : 0 < T) (y : Mechanism)
    (hfeas : Feasible E T y) (hwd : WellDefined E lamD lamS T y)
    (φhat : ℝ × ℝ) (hφ : φhat ∈ buyerTypes E T) (φ : ℝ × ℝ) :
    Eminus E lamD lamS T y φhat (Ud b φ) =
      φ.2 * Eminus E lamD lamS T y φhat (fun o => o.m) - Eminus E lamD lamS T y φhat (fun o => o.p)
        - b * Eminus E lamD lamS T y φhat (fun o => o.s - φ.1) := by
  obtain ⟨im, is, ip⟩ := comp_integrable E lamD lamS T hT y hfeas hwd φhat hφ
  have := P_prob E lamD lamS T hT
  unfold Eminus Ud
  have i1 := im.const_mul φ.2
  have i2 : Integrable (fun ω => b * (((y (φhat ::ₘ Hd ω) (Hs ω)).1 φhat).s - φ.1))
      (P E lamD lamS T) := (is.sub (integrable_const φ.1)).const_mul b
  have i12 : Integrable (fun ω => φ.2 * ((y (φhat ::ₘ Hd ω) (Hs ω)).1 φhat).m -
      ((y (φhat ::ₘ Hd ω) (Hs ω)).1 φhat).p) (P E lamD lamS T) := i1.sub ip
  rw [integral_sub i12 i2, integral_sub i1 ip, integral_const_mul, integral_const_mul]

lemma riemann_bound (Q U : ℝ → ℝ) (lo hi v : ℝ) (hv : v ∈ Set.Icc lo hi)
    (hQ : MonotoneOn Q (Set.Icc lo hi))
    (hU : ∀ x ∈ Set.Icc lo hi, ∀ x' ∈ Set.Icc lo hi, U x' + (x - x') * Q x' ≤ U x) :
    IntervalIntegrable Q volume lo v ∧ ∫ x in lo..v, Q x ≤ U v - U lo := by
  have hlv : lo ≤ v := hv.1
  have hsub : Set.uIcc lo v ⊆ Set.Icc lo hi := by
    rw [Set.uIcc_of_le hlv]; exact Set.Icc_subset_Icc le_rfl hv.2
  have hint : IntervalIntegrable Q volume lo v := (hQ.mono hsub).intervalIntegrable
  refine ⟨hint, ?_⟩
  set d := v - lo with hd
  have hd0 : 0 ≤ d := by linarith
  have hQd : 0 ≤ Q v - Q lo := sub_nonneg.2 (hQ ⟨le_rfl, hlv.trans hv.2⟩ ⟨hlv, hv.2⟩ hlv)
  have key : ∀ N : ℕ, 0 < N → (∫ x in lo..v, Q x) - (U v - U lo) ≤ d * (Q v - Q lo) / N := by
    intro N hN
    have hNr : (0:ℝ) < N := by exact_mod_cast hN
    let x : ℕ → ℝ := fun k => lo + k * d / N
    have hx0 : x 0 = lo := by simp [x]
    have hxN : x N = v := by simp only [x]; field_simp; ring
    have hxmem : ∀ k, k ≤ N → x k ∈ Set.Icc lo hi := by
      intro k hk
      have hk' : (k:ℝ) ≤ N := by exact_mod_cast hk
      have a1 : 0 ≤ (k:ℝ) * d / N := by positivity
      have a2 : (k:ℝ) * d / N ≤ d := by
        rw [div_le_iff₀ hNr]; nlinarith
      exact ⟨by simp only [x]; linarith, by simp only [x]; linarith [hv.2]⟩
    have hstep : ∀ k, x (k + 1) - x k = d / N := by
      intro k; simp only [x]; push_cast; ring
    have hmono : ∀ k, x k ≤ x (k + 1) := by
      intro k; have := hstep k; have : 0 ≤ d / N := by positivity
      linarith
    have hsubk : ∀ k, k < N → Set.uIcc (x k) (x (k+1)) ⊆ Set.Icc lo hi := by
      intro k hk
      rw [Set.uIcc_of_le (hmono k)]
      exact Set.Icc_subset_Icc (hxmem k hk.le).1 (hxmem (k+1) hk).2
    have hintk : ∀ k < N, IntervalIntegrable Q volume (x k) (x (k + 1)) := fun k hk =>
      (hQ.mono (hsubk k hk)).intervalIntegrable
    have hsumI := intervalIntegral.sum_integral_adjacent_intervals hintk
    rw [hx0, hxN] at hsumI
    have hsumU : ∑ k ∈ Finset.range N, (U (x (k+1)) - U (x k)) = U v - U lo := by
      rw [Finset.sum_range_sub (fun k => U (x k)), hxN, hx0]
    have hsumQ : ∑ k ∈ Finset.range N, (Q (x (k+1)) - Q (x k)) = Q v - Q lo := by
      rw [Finset.sum_range_sub (fun k => Q (x k)), hxN, hx0]
    have hI : ∀ k ∈ Finset.range N, ∫ t in x k..x (k+1), Q t ≤ d / N * Q (x (k+1)) := by
      intro k hk
      have hk' := Finset.mem_range.1 hk
      have := intervalIntegral.integral_mono_on (hmono k) (hintk k hk')
        (intervalIntegrable_const (c := Q (x (k+1))))
        (fun t ht => hQ ⟨(hxmem k hk'.le).1.trans ht.1, ht.2.trans (hxmem (k+1) hk').2⟩
          (hxmem (k+1) hk') ht.2)
      rw [intervalIntegral.integral_const, smul_eq_mul, hstep] at this
      exact this
    have hUk : ∀ k ∈ Finset.range N, d / N * Q (x k) ≤ U (x (k+1)) - U (x k) := by
      intro k hk
      have hk' := Finset.mem_range.1 hk
      have := hU (x (k+1)) (hxmem (k+1) hk') (x k) (hxmem k hk'.le)
      rw [hstep] at this
      linarith
    have s1 := Finset.sum_le_sum hI
    have s2 := Finset.sum_le_sum hUk
    rw [hsumI] at s1
    rw [hsumU] at s2
    have e3 : ∑ k ∈ Finset.range N, d / N * Q (x (k+1)) - ∑ k ∈ Finset.range N, d / N * Q (x k)
        = d / N * (Q v - Q lo) := by
      rw [← Finset.sum_sub_distrib, ← hsumQ, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k _ => by ring)
    have e4 : d / N * (Q v - Q lo) = d * (Q v - Q lo) / N := by ring
    linarith
  by_contra hcon
  push_neg at hcon
  set c := (∫ x in lo..v, Q x) - (U v - U lo) with hc
  have hc0 : 0 < c := by linarith
  obtain ⟨N, hN⟩ := exists_nat_gt (d * (Q v - Q lo) / c)
  have hNpos : (0:ℝ) < N := lt_of_le_of_lt (by positivity) hN
  have hN' : 0 < N := by exact_mod_cast hNpos
  have h1 := key N hN'
  have h2 : d * (Q v - Q lo) / N < c := by
    rw [div_lt_iff₀ hNpos]
    rw [div_lt_iff₀ hc0] at hN
    linarith
  linarith

end TwoSidedMatching.MechBound.S1Aux

open TwoSidedMatching.MechBound TwoSidedMatching.MechBound.S1Aux

theorem solution
    (E : Environment)
    (hfB : ContinuousOn E.fB (Set.Icc E.loB E.hiB))
    (hfS : ContinuousOn E.fS (Set.Icc E.loS E.hiS))
    (hreg : E.Regular) (hcv : E.loS ≤ E.hiB)
    (lamD lamS T b h : ℝ) (hlamD : 0 < lamD) (hlamS : 0 < lamS) (hT : 0 < T)
    (hb : 0 ≤ b) (hh : 0 ≤ h)
    (y : Mechanism) (hfeas : Feasible E T y) (hwd : WellDefined E lamD lamS T y)
    (hIC : ICd' E lamD lamS T b y) (hIR : IRd E lamD lamS T b y) :
    ∀ φ ∈ buyerTypes E T,
      IntervalIntegrable (fun v' => Eminus E lamD lamS T y (φ.1, v') (fun o => o.m))
          volume E.loB φ.2 ∧
      Eminus E lamD lamS T y φ (fun o => o.p) ≤
        φ.2 * Eminus E lamD lamS T y φ (fun o => o.m) -
          (∫ v' in E.loB..φ.2, Eminus E lamD lamS T y (φ.1, v') (fun o => o.m)) -
          b * Eminus E lamD lamS T y φ (fun o => o.s - φ.1) := by
  rintro ⟨t, v⟩ hφ
  simp only
  have ht : t ∈ Set.Icc 0 T := hφ.1
  have hv : v ∈ Set.Icc E.loB E.hiB := hφ.2
  have mem : ∀ w ∈ Set.Icc E.loB E.hiB, (t, w) ∈ buyerTypes E T := fun w hw => ⟨ht, hw⟩
  set Q : ℝ → ℝ := fun w => Eminus E lamD lamS T y (t, w) (fun o => o.m) with hQdef
  set Pp : ℝ → ℝ := fun w => Eminus E lamD lamS T y (t, w) (fun o => o.p) with hPdef
  set W : ℝ → ℝ := fun w => Eminus E lamD lamS T y (t, w) (fun o => o.s - t) with hWdef
  set U : ℝ → ℝ := fun w => w * Q w - Pp w - b * W w with hUdef
  have hIC2 : ∀ x ∈ Set.Icc E.loB E.hiB, ∀ x' ∈ Set.Icc E.loB E.hiB,
      x * Q x' - Pp x' - b * W x' ≤ U x := by
    intro x hx x' hx'
    have := hIC (t, x) (mem x hx) x' hx'
    rw [Eminus_Ud E lamD lamS T b hT y hfeas hwd _ (mem x' hx'),
      Eminus_Ud E lamD lamS T b hT y hfeas hwd _ (mem x hx)] at this
    exact this
  have hU : ∀ x ∈ Set.Icc E.loB E.hiB, ∀ x' ∈ Set.Icc E.loB E.hiB,
      U x' + (x - x') * Q x' ≤ U x := by
    intro x hx x' hx'
    have := hIC2 x hx x' hx'
    simp only [hUdef]
    linarith
  have hQmono : MonotoneOn Q (Set.Icc E.loB E.hiB) := by
    intro x' hx' x hx hle
    have a1 := hU x hx x' hx'
    have a2 := hU x' hx' x hx
    by_cases heq : x' = x
    · rw [heq]
    · have hlt : 0 < x - x' := by
        have := lt_of_le_of_ne hle heq; linarith
      have : (x - x') * Q x' ≤ (x - x') * Q x := by nlinarith
      exact le_of_mul_le_mul_left this hlt
  have hlo : E.loB ∈ Set.Icc E.loB E.hiB := ⟨le_rfl, E.loB_lt_hiB.le⟩
  have hIRlo : 0 ≤ U E.loB := by
    have := hIR (t, E.loB) (mem _ hlo)
    rw [Eminus_Ud E lamD lamS T b hT y hfeas hwd _ (mem _ hlo)] at this
    exact this
  obtain ⟨hint, hbound⟩ := riemann_bound Q U E.loB E.hiB v hv hQmono hU
  refine ⟨hint, ?_⟩
  show Pp v ≤ v * Q v - (∫ v' in E.loB..v, Q v') - b * W v
  have : U v = v * Q v - Pp v - b * W v := rfl
  linarith
