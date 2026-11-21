-- Prove2me | solution 1 for ProdMomentConc.lemma_2_3
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-21T02:50:41.192098+00:00
-- url     : https://prove2.me/submissions/be3d5f98-e6f0-4b2a-a039-6cb7ef5df4fb

import Mathlib
import Definitions.Def_ProdMomentConc_kSubsetLaw

open MeasureTheory ProbabilityTheory

namespace ProdMomentConc

private lemma integral_uniformOn_finset_real
    {α : Type*} [Fintype α] [DecidableEq α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (A : Finset α) (_hA : A.Nonempty) (f : α → ℝ) :
    (∫ x, f x ∂(uniformOn (A : Set α))) =
      (∑ x ∈ A, f x) / (A.card : ℝ) := by
  classical
  have hmeasure (x : α) :
      ((uniformOn (A : Set α)) {x}).toReal =
        if x ∈ A then (A.card : ℝ)⁻¹ else 0 := by
    rw [show ({x} : Set α) = (({x} : Finset α) : Set α) by
      ext y
      simp]
    rw [uniformOn_apply_finset, Finset.inter_singleton]
    by_cases hx : x ∈ A
    · simp [hx, ENNReal.toReal_natCast, div_eq_mul_inv]
    · simp [hx]
  have : IsProbabilityMeasure (uniformOn (A : Set α)) :=
    isProbabilityMeasure_uniformOn A.finite_toSet _hA
  rw [integral_fintype (f := f) (μ := uniformOn (A : Set α)) Integrable.of_finite]
  simp only [measureReal_def, hmeasure, smul_eq_mul, ite_mul, zero_mul]
  have hsum :
      (∑ x : α, if x ∈ A then (A.card : ℝ)⁻¹ * f x else 0) =
        ∑ x ∈ A, (A.card : ℝ)⁻¹ * f x := by
    let g : α → ℝ := fun x =>
      if x ∈ A then (A.card : ℝ)⁻¹ * f x else 0
    have hsub : (∑ x ∈ A, g x) = ∑ x ∈ Finset.univ, g x := by
      apply Finset.sum_subset (Finset.subset_univ A)
      intro x _hx hxA
      simp [g, hxA]
    calc
      _ = ∑ x ∈ Finset.univ, g x := by rfl
      _ = ∑ x ∈ A, g x := hsub.symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro x hx
        simp [g, hx]
  rw [hsum, ← Finset.mul_sum]
  simp [div_eq_mul_inv, mul_comm]

private lemma card_filter_powersetCard_succ (n k : ℕ) (i : Fin (n + 1)) :
    (((Finset.univ : Finset (Fin (n + 1))).powersetCard (k + 1)).filter
      (fun S => i ∈ S)).card = n.choose k := by
  classical
  let U : Finset (Fin (n + 1)) := Finset.univ.erase i
  have hiU : i ∉ U := by
    simp [U]
  have h_avoid {T : Finset (Fin (n + 1))}
      (hT : T ∈ U.powersetCard k) : i ∉ T := by
    intro hiT
    have hsub := (Finset.mem_powersetCard.mp hT).1
    exact hiU (hsub hiT)
  have hfilter :
      ((Finset.univ : Finset (Fin (n + 1))).powersetCard (k + 1)).filter
          (fun S => i ∈ S) =
        (U.powersetCard k).image (fun T => insert i T) := by
    ext S
    constructor
    · intro hS
      rcases Finset.mem_filter.mp hS with ⟨hSpow, hiS⟩
      have hcardS : S.card = k + 1 :=
        (Finset.mem_powersetCard.mp hSpow).2
      refine Finset.mem_image.mpr ⟨S.erase i, ?_, ?_⟩
      · apply Finset.mem_powersetCard.mpr
        constructor
        · intro x hx
          have hx' := Finset.mem_erase.mp hx
          simp only [U, Finset.mem_erase, Finset.mem_univ, and_true]
          exact hx'.1
        · rw [Finset.card_erase_of_mem hiS, hcardS]
          simp
      · exact Finset.insert_erase hiS
    · intro hS
      obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hS
      have hT' := Finset.mem_powersetCard.mp hT
      have hiT : i ∉ T := h_avoid hT
      refine Finset.mem_filter.mpr ⟨?_, Finset.mem_insert_self _ _⟩
      refine Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, ?_⟩
      rw [Finset.card_insert_of_notMem hiT, hT'.2]
  have hinj :
      Set.InjOn (fun T : Finset (Fin (n + 1)) => insert i T)
        (U.powersetCard k : Set (Finset (Fin (n + 1)))) := by
    intro T hT V hV hEq
    have hiT : i ∉ T := h_avoid (by simpa using hT)
    have hiV : i ∉ V := h_avoid (by simpa using hV)
    have h := congrArg (fun W : Finset (Fin (n + 1)) => W.erase i) hEq
    simpa [hiT, hiV] using h
  rw [hfilter]
  calc
    ((U.powersetCard k).image (fun T => insert i T)).card =
        (U.powersetCard k).card := Finset.card_image_iff.mpr hinj
    _ = U.card.choose k := by rw [Finset.card_powersetCard]
    _ = n.choose k := by simp [U]

private lemma sum_mem_eq_sum_ite {n : ℕ} (S : Finset (Fin n))
    (f : Fin n → ℝ) :
    (∑ i ∈ S, f i) = ∑ i : Fin n, if i ∈ S then f i else 0 := by
  classical
  let g : Fin n → ℝ := fun i => if i ∈ S then f i else 0
  have hsub : (∑ i ∈ S, g i) = ∑ i ∈ Finset.univ, g i := by
    apply Finset.sum_subset (Finset.subset_univ S)
    intro i _hi hiS
    simp [g, hiS]
  calc
    (∑ i ∈ S, f i) = ∑ i ∈ S, g i := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [g, hi]
    _ = ∑ i ∈ Finset.univ, g i := hsub
    _ = _ := by rfl

private lemma exp_average_le {ι : Type*} (A : Finset ι) (hA : A.Nonempty)
    (f : ι → ℝ) :
    Real.exp ((∑ i ∈ A, f i) / (A.card : ℝ)) ≤
      (∑ i ∈ A, Real.exp (f i)) / (A.card : ℝ) := by
  classical
  have hcard : 0 < (A.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hA
  let w : ι → ℝ := fun _ => (A.card : ℝ)⁻¹
  have hw : ∀ i ∈ A, 0 ≤ w i := by
    intro i _hi
    dsimp [w]
    positivity
  have hsumw : ∑ i ∈ A, w i = 1 := by
    simp [w, hcard.ne']
  have hJ : Real.exp (∑ i ∈ A, w i * f i) ≤ ∑ i ∈ A, w i * Real.exp (f i) := by
    have hconv : ConvexOn ℝ Set.univ Real.exp := convexOn_exp
    have hw' : ∀ i ∈ A, 0 ≤ w i := hw
    have hsumw' : ∑ i ∈ A, w i = 1 := hsumw
    have hmem : ∀ i ∈ A, f i ∈ Set.univ := fun i _ => Set.mem_univ _
    have := hconv.map_sum_le hw' hsumw' hmem
    simpa using this
  have hleft :
      (∑ i ∈ A, w i • f i) = (∑ i ∈ A, f i) / (A.card : ℝ) := by
    calc
      (∑ i ∈ A, w i • f i) = (A.card : ℝ)⁻¹ * ∑ i ∈ A, f i := by
        simp only [w, smul_eq_mul, ← Finset.mul_sum]
      _ = _ := by
        rw [div_eq_mul_inv]
        exact mul_comm _ _
  have hright :
      (∑ i ∈ A, w i • Real.exp (f i)) =
        (∑ i ∈ A, Real.exp (f i)) / (A.card : ℝ) := by
    calc
      (∑ i ∈ A, w i • Real.exp (f i)) =
          (A.card : ℝ)⁻¹ * ∑ i ∈ A, Real.exp (f i) := by
        simp only [w, smul_eq_mul, ← Finset.mul_sum]
      _ = _ := by
        rw [div_eq_mul_inv]
        exact mul_comm _ _
  rw [← hleft, ← hright]
  exact hJ

theorem _root_.solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {n : ℕ} (X : Fin n → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (α : ℝ) (k : ℕ)
    (hk : 1 ≤ k) (hkn : k ≤ n) (t : ℝ) (ht : 0 < t) :
    μ {ω | α * (n : ℝ) ≤ ∑ i, X i ω} ≤
      ENNReal.ofReal (Real.exp (-(t * α * (k : ℝ)))) *
        ∫⁻ S, ∫⁻ ω, ENNReal.ofReal (Real.exp (t * ∑ i ∈ S, X i ω))
          ∂μ ∂(kSubsetLaw n k) := by
  classical
  cases k with
  | zero => omega
  | succ k =>
      cases n with
      | zero => omega
      | succ n =>
          let A : Finset (Finset (Fin (n + 1))) :=
            Finset.univ.powersetCard (k + 1)
          have hAcard : A.card = (n + 1).choose (k + 1) := by
            simp [A, Finset.card_powersetCard]
          have hCnat : 0 < (n + 1).choose (k + 1) :=
            Nat.choose_pos hkn
          have hApos : 0 < A.card := by
            simpa [hAcard] using hCnat
          have hA : A.Nonempty := Finset.card_pos.mp hApos
          have hlaw : kSubsetLaw (n + 1) (k + 1) =
              uniformOn (A : Set (Finset (Fin (n + 1)))) := by
            unfold kSubsetLaw
            apply congrArg uniformOn
            ext S
            simp [A, Finset.mem_powersetCard]
          have : IsProbabilityMeasure (kSubsetLaw (n + 1) (k + 1)) := by
            rw [hlaw]
            exact isProbabilityMeasure_uniformOn A.finite_toSet hA
          have hcount (i : Fin (n + 1)) :
              (A.filter (fun S => i ∈ S)).card = n.choose k := by
            simpa [A] using card_filter_powersetCard_succ n k i
          have hdouble (z : Fin (n + 1) → ℝ) :
              (∑ S ∈ A, ∑ i ∈ S, z i) =
                (n.choose k : ℝ) * ∑ i, z i := by
            have hterm (i : Fin (n + 1)) :
                (∑ S ∈ A, if i ∈ S then z i else 0) =
                  (n.choose k : ℝ) * z i := by
              calc
                (∑ S ∈ A, if i ∈ S then z i else 0) =
                    ∑ S ∈ A.filter (fun S => i ∈ S), z i := by
                  rw [Finset.sum_filter]
                _ = (n.choose k : ℝ) * z i := by
                  simp [hcount i, nsmul_eq_mul]
            calc
              (∑ S ∈ A, ∑ i ∈ S, z i) =
                  ∑ S ∈ A, ∑ i : Fin (n + 1),
                    if i ∈ S then z i else 0 := by
                apply Finset.sum_congr rfl
                intro S _hS
                exact sum_mem_eq_sum_ite S z
              _ = ∑ i : Fin (n + 1), ∑ S ∈ A,
                    if i ∈ S then z i else 0 := by
                exact Finset.sum_comm
              _ = ∑ i : Fin (n + 1), (n.choose k : ℝ) * z i := by
                apply Finset.sum_congr rfl
                intro i _hi
                exact hterm i
              _ = (n.choose k : ℝ) * ∑ i : Fin (n + 1), z i := by
                rw [Finset.mul_sum]
          have hsumt (ω : Ω) :
              (∑ S ∈ A, t * ∑ i ∈ S, X i ω) =
                t * (n.choose k : ℝ) * ∑ i, X i ω := by
            rw [← Finset.mul_sum, hdouble]
            ring
          have hC :
              ((((n + 1).choose (k + 1) : ℕ) : ℝ)) ≠ 0 := by
            exact_mod_cast (Nat.ne_of_gt hCnat)
          have hN : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by
            positivity
          have hchoose :
              (((n + 1 : ℕ) : ℝ) * (n.choose k : ℝ)) =
                ((((n + 1).choose (k + 1) : ℕ) : ℝ) *
                  ((k + 1 : ℕ) : ℝ)) := by
            exact_mod_cast (Nat.add_one_mul_choose_eq n k)
          have hratio :
              (n.choose k : ℝ) / (A.card : ℝ) =
                ((k + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ) := by
            rw [hAcard, div_eq_div_iff hC hN]
            linear_combination hchoose
          have havg (ω : Ω) :
              (∑ S ∈ A, t * ∑ i ∈ S, X i ω) / (A.card : ℝ) =
                t * (((k + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) *
                  ∑ i, X i ω := by
            calc
              (∑ S ∈ A, t * ∑ i ∈ S, X i ω) / (A.card : ℝ) =
                  (t * (n.choose k : ℝ) * ∑ i, X i ω) / (A.card : ℝ) := by
                rw [hsumt]
              _ = t * ((n.choose k : ℝ) / (A.card : ℝ)) * ∑ i, X i ω := by
                ring
              _ = _ := by rw [hratio]
          have hJensen (ω : Ω) :
              Real.exp ((∑ S ∈ A, t * ∑ i ∈ S, X i ω) / (A.card : ℝ)) ≤
                (∑ S ∈ A, Real.exp (t * ∑ i ∈ S, X i ω)) / (A.card : ℝ) :=
            exp_average_le A hA (fun S => t * ∑ i ∈ S, X i ω)
          have hexponent (ω : Ω)
              (hω : α * ((n + 1 : ℕ) : ℝ) ≤ ∑ i, X i ω) :
              t * α * ((k + 1 : ℕ) : ℝ) ≤
                (∑ S ∈ A, t * ∑ i ∈ S, X i ω) / (A.card : ℝ) := by
            rw [havg]
            have hfactor :
                0 ≤ t * (((k + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) := by
              positivity
            calc
              t * α * ((k + 1 : ℕ) : ℝ) =
                  (t * (((k + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ))) *
                    (α * ((n + 1 : ℕ) : ℝ)) := by
                field_simp [hN]
                <;> ring
              _ ≤ (t * (((k + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ))) *
                    (∑ i, X i ω) :=
                mul_le_mul_of_nonneg_left hω hfactor
              _ = _ := by ring
          let E : Set Ω :=
            {ω | α * ((n + 1 : ℕ) : ℝ) ≤ ∑ i, X i ω}
          have hreal (ω : Ω) (hω : ω ∈ E) :
              Real.exp (t * α * ((k + 1 : ℕ) : ℝ)) ≤
                ∫ S, Real.exp (t * ∑ i ∈ S, X i ω)
                  ∂(kSubsetLaw (n + 1) (k + 1)) := by
            have hω' : α * ((n + 1 : ℕ) : ℝ) ≤ ∑ i, X i ω := by
              simpa [E] using hω
            rw [hlaw, integral_uniformOn_finset_real A hA
              (fun S => Real.exp (t * ∑ i ∈ S, X i ω))]
            exact (Real.exp_le_exp.mpr (hexponent ω hω')).trans (hJensen ω)
          have hconvert (ω : Ω) :
              ENNReal.ofReal
                  (∫ S, Real.exp (t * ∑ i ∈ S, X i ω)
                    ∂(kSubsetLaw (n + 1) (k + 1))) =
                ∫⁻ S, ENNReal.ofReal (Real.exp (t * ∑ i ∈ S, X i ω))
                  ∂(kSubsetLaw (n + 1) (k + 1)) := by
            apply ofReal_integral_eq_lintegral_ofReal
            · exact Integrable.of_finite
            · exact Filter.Eventually.of_forall
                (fun S => (Real.exp_pos (t * ∑ i ∈ S, X i ω)).le)
          have hpoint (ω : Ω) :
              E.indicator
                  (fun _ => ENNReal.ofReal
                    (Real.exp (t * α * ((k + 1 : ℕ) : ℝ)))) ω ≤
                ∫⁻ S, ENNReal.ofReal (Real.exp (t * ∑ i ∈ S, X i ω))
                  ∂(kSubsetLaw (n + 1) (k + 1)) := by
            by_cases hω : ω ∈ E
            · simp only [Set.indicator_of_mem hω]
              calc
                ENNReal.ofReal (Real.exp (t * α * ((k + 1 : ℕ) : ℝ))) ≤
                    ENNReal.ofReal
                      (∫ S, Real.exp (t * ∑ i ∈ S, X i ω)
                        ∂(kSubsetLaw (n + 1) (k + 1))) :=
                  ENNReal.ofReal_le_ofReal (hreal ω hω)
                _ = _ := hconvert ω
            · simp [Set.indicator, hω]
          have hsumΩ : Measurable (fun ω => ∑ i, X i ω) := by
            apply Finset.measurable_sum
            intro i _hi
            exact hX i
          have hE : MeasurableSet E := by
            change MeasurableSet
              {ω | α * ((n + 1 : ℕ) : ℝ) ≤ ∑ i, X i ω}
            exact measurableSet_le measurable_const hsumΩ
          have hInt :
              ENNReal.ofReal (Real.exp (t * α * ((k + 1 : ℕ) : ℝ))) * μ E ≤
                ∫⁻ ω, ∫⁻ S,
                  ENNReal.ofReal (Real.exp (t * ∑ i ∈ S, X i ω))
                    ∂(kSubsetLaw (n + 1) (k + 1)) ∂μ := by
            have hmono :
                (∫⁻ ω, E.indicator
                    (fun _ => ENNReal.ofReal
                      (Real.exp (t * α * ((k + 1 : ℕ) : ℝ)))) ω ∂μ) ≤
                  ∫⁻ ω, ∫⁻ S,
                    ENNReal.ofReal (Real.exp (t * ∑ i ∈ S, X i ω))
                      ∂(kSubsetLaw (n + 1) (k + 1)) ∂μ :=
              lintegral_mono (fun ω => hpoint ω)
            rw [lintegral_indicator hE, setLIntegral_const] at hmono
            simpa [mul_comm] using hmono
          have hsumjoint : Measurable
              (fun p : Ω × Finset (Fin (n + 1)) =>
                ∑ i ∈ p.2, X i p.1) := by
            have heq :
                (fun p : Ω × Finset (Fin (n + 1)) =>
                  ∑ i ∈ p.2, X i p.1) =
                  (fun p => ∑ i : Fin (n + 1),
                    if i ∈ p.2 then X i p.1 else 0) := by
              funext p
              exact sum_mem_eq_sum_ite p.2 (fun i => X i p.1)
            rw [heq]
            apply Finset.measurable_sum
            intro i _hi
            have hpre : MeasurableSet {S : Finset (Fin (n + 1)) | i ∈ S} :=
              (Set.toFinite _).measurableSet
            have hmem :
                MeasurableSet {p : Ω × Finset (Fin (n + 1)) | i ∈ p.2} := by
              change MeasurableSet
                (Prod.snd ⁻¹' {S : Finset (Fin (n + 1)) | i ∈ S})
              exact measurable_snd hpre
            have hXi :
                Measurable (fun p : Ω × Finset (Fin (n + 1)) => X i p.1) :=
              (hX i).comp measurable_fst
            have hind := hXi.indicator hmem
            convert hind using 1
            ext p
            simp only [Set.mem_ofPred_eq, Set.indicator_apply]
          have hjoint : Measurable (Function.uncurry
              (fun (ω : Ω) (S : Finset (Fin (n + 1))) =>
                ENNReal.ofReal (Real.exp (t * ∑ i ∈ S, X i ω)))) := by
            have hrealjoint : Measurable
                (fun p : Ω × Finset (Fin (n + 1)) =>
                  Real.exp (t * ∑ i ∈ p.2, X i p.1)) :=
              Real.measurable_exp.comp (measurable_const.mul hsumjoint)
            exact ENNReal.measurable_ofReal.comp hrealjoint
          have hswap :
              (∫⁻ ω, ∫⁻ S,
                  ENNReal.ofReal (Real.exp (t * ∑ i ∈ S, X i ω))
                    ∂(kSubsetLaw (n + 1) (k + 1)) ∂μ) =
                ∫⁻ S, ∫⁻ ω,
                  ENNReal.ofReal (Real.exp (t * ∑ i ∈ S, X i ω))
                    ∂μ ∂(kSubsetLaw (n + 1) (k + 1)) :=
            lintegral_lintegral_swap hjoint.aemeasurable
          have hbound :
              ENNReal.ofReal (Real.exp (t * α * ((k + 1 : ℕ) : ℝ))) * μ E ≤
                ∫⁻ S, ∫⁻ ω,
                  ENNReal.ofReal (Real.exp (t * ∑ i ∈ S, X i ω))
                    ∂μ ∂(kSubsetLaw (n + 1) (k + 1)) :=
            hInt.trans_eq hswap
          have hcd :
              ENNReal.ofReal (Real.exp (-(t * α * ((k + 1 : ℕ) : ℝ)))) *
                  ENNReal.ofReal (Real.exp (t * α * ((k + 1 : ℕ) : ℝ))) = 1 := by
            rw [← ENNReal.ofReal_mul (Real.exp_nonneg _)]
            rw [← Real.exp_add]
            simp
          change μ E ≤
            ENNReal.ofReal (Real.exp (-(t * α * ((k + 1 : ℕ) : ℝ)))) *
              ∫⁻ S, ∫⁻ ω,
                ENNReal.ofReal (Real.exp (t * ∑ i ∈ S, X i ω))
                  ∂μ ∂(kSubsetLaw (n + 1) (k + 1))
          calc
            μ E = 1 * μ E := (one_mul _).symm
            _ = (ENNReal.ofReal
                    (Real.exp (-(t * α * ((k + 1 : ℕ) : ℝ)))) *
                  ENNReal.ofReal
                    (Real.exp (t * α * ((k + 1 : ℕ) : ℝ)))) * μ E := by
              rw [hcd]
            _ = ENNReal.ofReal
                  (Real.exp (-(t * α * ((k + 1 : ℕ) : ℝ)))) *
                (ENNReal.ofReal
                  (Real.exp (t * α * ((k + 1 : ℕ) : ℝ))) * μ E) :=
              mul_assoc _ _ _
            _ ≤ ENNReal.ofReal
                  (Real.exp (-(t * α * ((k + 1 : ℕ) : ℝ)))) *
                (∫⁻ S, ∫⁻ ω,
                  ENNReal.ofReal (Real.exp (t * ∑ i ∈ S, X i ω))
                    ∂μ ∂(kSubsetLaw (n + 1) (k + 1))) :=
              mul_le_mul_of_nonneg_left hbound (by positivity)

end ProdMomentConc
