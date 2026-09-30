-- Prove2me | solution 1 for UnderstandingML.multiclass_realizable_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-25T22:40:43.309773+00:00
-- url     : https://prove2.me/submissions/a4cd923e-8c14-46f0-b993-f239e6b08f67

import Definitions.Def_UnderstandingML_MulticlassLearnability
import Theorems.Thm_UnderstandingML_natarajan_lemma
import Mathlib

open MeasureTheory UnderstandingML

universe u v

namespace RealizableUpperAux

open Classical

section Basic

variable {Z : Type*}

/-- Number of sample points falling in `E`. -/
noncomputable def cnt {m : ℕ} (E : Set Z) (S : Fin m → Z) : ℕ := ∑ i, if S i ∈ E then 1 else 0

/-- Coordinatewise swap of a double sample. -/
def swapAt {m : ℕ} (σ : Fin m → Bool) (w : Fin m → Z × Z) : Fin m → Z × Z :=
  fun i ↦ if σ i then (w i).swap else w i

/-- The swaps making a fixed error pattern consistent on the first half with at least `r` errors
on the second half are at most `2^(m-r)`. -/
lemma pattern_swaps {m : ℕ} (π : Fin m → Bool × Bool) (r : ℕ) :
    (Finset.univ.filter (fun σ : Fin m → Bool ↦
      (∀ i, (if σ i then (π i).2 else (π i).1) = false) ∧
      r ≤ ∑ i, (if (if σ i then (π i).1 else (π i).2) = true then 1 else 0))).card ≤
      2 ^ (m - r) := by
  set T := (Finset.univ.filter (fun σ : Fin m → Bool ↦
      (∀ i, (if σ i then (π i).2 else (π i).1) = false) ∧
      r ≤ ∑ i, (if (if σ i then (π i).1 else (π i).2) = true then 1 else 0))) with hT
  set I : Finset (Fin m) := Finset.univ.filter (fun i ↦ (π i).1 ≠ (π i).2) with hI
  have hA : ∀ σ ∈ T, ∀ i ∈ I, σ i = (π i).1 := by
    intro σ hσ i hi
    have h1 := (Finset.mem_filter.1 hσ).2.1 i
    have h2 := (Finset.mem_filter.1 hi).2
    revert h1 h2
    cases σ i <;> cases (π i).1 <;> cases (π i).2 <;> simp
  have hB : ∀ σ ∈ T, r ≤ I.card := by
    intro σ hσ
    have h := (Finset.mem_filter.1 hσ).2
    refine h.2.trans ?_
    rw [Finset.card_filter]
    refine Finset.sum_le_sum fun i _ ↦ ?_
    have h1 := h.1 i
    revert h1
    cases σ i <;> cases (π i).1 <;> cases (π i).2 <;> simp
  rcases T.eq_empty_or_nonempty with hTe | ⟨σ₀, hσ₀⟩
  · rw [hTe]; simp
  have hrI := hB σ₀ hσ₀
  have hIm : I.card ≤ m := by
    simpa using Finset.card_le_univ I
  calc T.card ≤ (Finset.univ : Finset ({i // i ∉ I} → Bool)).card := by
        refine Finset.card_le_card_of_injOn (fun σ i ↦ σ i.1) (fun _ _ ↦ Finset.mem_univ _) ?_
        intro σ hσ σ' hσ' heq
        funext i
        by_cases hi : i ∈ I
        · rw [hA σ hσ i hi, hA σ' hσ' i hi]
        · exact congrFun heq ⟨i, hi⟩
    _ = 2 ^ (m - I.card) := by
        rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool]
        congr 1
        rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe]
    _ ≤ 2 ^ (m - r) := Nat.pow_le_pow_right (by norm_num) (by omega)

lemma swap_count {m : ℕ} (w : Fin m → Z × Z) {J : Type*} (E : J → Set Z) (r : ℕ) :
    (Finset.univ.filter (fun σ : Fin m → Bool ↦ swapAt σ w ∈
      {w | ∃ j, (∀ i, (w i).1 ∉ E j) ∧ r ≤ cnt (E j) (fun i ↦ (w i).2)})).card ≤
      (Set.range (fun j i ↦ (decide ((w i).1 ∈ E j), decide ((w i).2 ∈ E j)))).ncard *
        2 ^ (m - r) := by
  set pat : J → Fin m → Bool × Bool :=
    fun j i ↦ (decide ((w i).1 ∈ E j), decide ((w i).2 ∈ E j)) with hpat
  have hfin : (Set.range pat).Finite := Set.toFinite _
  set T : (Fin m → Bool × Bool) → Finset (Fin m → Bool) := fun π ↦
    Finset.univ.filter (fun σ : Fin m → Bool ↦
      (∀ i, (if σ i then (π i).2 else (π i).1) = false) ∧
      r ≤ ∑ i, (if (if σ i then (π i).1 else (π i).2) = true then 1 else 0)) with hT
  calc _ ≤ (hfin.toFinset.biUnion T).card := by
        apply Finset.card_le_card
        intro σ hσ
        obtain ⟨j, hj1, hj2⟩ := (Finset.mem_filter.1 hσ).2
        rw [Finset.mem_biUnion]
        refine ⟨pat j, hfin.mem_toFinset.2 ⟨j, rfl⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_, ?_⟩⟩
        · intro i
          have := hj1 i
          simp only [swapAt] at this
          cases hσi : σ i <;> simp_all
        · refine hj2.trans (le_of_eq ?_)
          unfold cnt
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          cases hσi : σ i <;> simp [swapAt, hσi, hpat]
    _ ≤ ∑ π ∈ hfin.toFinset, (T π).card := Finset.card_biUnion_le
    _ ≤ ∑ π ∈ hfin.toFinset, 2 ^ (m - r) := Finset.sum_le_sum fun π _ ↦ pattern_swaps π r
    _ = _ := by rw [Finset.sum_const, smul_eq_mul, Set.ncard_eq_toFinset_card _ hfin]


end Basic

section Prob

variable {Z : Type*} [MeasurableSpace Z]

lemma measurable_cnt {m : ℕ} {E : Set Z} (hE : MeasurableSet E) :
    Measurable (fun S : Fin m → Z ↦ cnt E S) := by
  unfold cnt
  refine Finset.measurable_sum _ fun i _ ↦ ?_
  exact Measurable.ite (hE.preimage (measurable_pi_apply i)) measurable_const measurable_const

lemma chernoff_half (μ : Measure Z) [IsProbabilityMeasure μ] {E : Set Z} (hE : MeasurableSet E)
    {ε : ℝ} (hε : 0 < ε) (hεE : ENNReal.ofReal ε < μ E) (m : ℕ) (hm : 8 ≤ ε * m) :
    iidLaw μ m {S | cnt E S < ⌈ε * m / 2⌉₊} ≤ 1 / 2 := by
  set r := ⌈ε * m / 2⌉₊ with hr
  rcases Nat.eq_zero_or_pos r with hr0 | hr0
  · have : {S : Fin m → Z | cnt E S < r} = ∅ := by ext S; simp [hr0]
    rw [this, measure_empty]; exact bot_le
  set ν := iidLaw μ m with hν
  have : IsProbabilityMeasure ν := by rw [hν, iidLaw]; infer_instance
  set p := (μ E).toReal with hp
  have hμE : μ E ≠ ⊤ := measure_ne_top _ _
  have hεp : ε < p := by
    rw [hp]; exact (ENNReal.ofReal_lt_iff_lt_toReal hε.le hμE).1 hεE
  have hp1 : p ≤ 1 := by
    rw [hp]; exact ENNReal.toReal_le_of_le_ofReal zero_le_one
      (by rw [ENNReal.ofReal_one]; exact prob_le_one)
  set g : Z → ℝ := fun z ↦ if z ∈ E then 1 / 2 else 1 with hg
  set F : (Fin m → Z) → ℝ := fun S ↦ ∏ i, g (S i) with hF
  have hgm : Measurable g := Measurable.ite hE measurable_const measurable_const
  have hint_g : ∫ z, g z ∂μ = 1 - p / 2 := by
    have : g = fun z ↦ 1 - (1 / 2) * E.indicator (fun _ ↦ (1:ℝ)) z := by
      funext z; simp only [hg, Set.indicator_apply]; split_ifs <;> norm_num
    rw [this, integral_sub (integrable_const _) ((Integrable.indicator (integrable_const _) hE).const_mul _),
      integral_const_mul, integral_indicator hE, setIntegral_const]
    simp [hp, Measure.real]
    ring
  have hEF : ∫ S, F S ∂ν = (1 - p / 2) ^ m := by
    rw [hF, hν, iidLaw, integral_fintype_prod_eq_pow, hint_g, Fintype.card_fin]
  have hFcnt : ∀ S, F S = (1 / 2 : ℝ) ^ cnt E S := by
    intro S
    simp only [hF, hg, cnt]
    rw [← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    split_ifs <;> simp
  set c : ℝ := (1 / 2) ^ (r - 1) with hc
  have hsub : {S | cnt E S < r} ⊆ {S | c ≤ F S} := by
    intro S hS
    simp only [Set.mem_ofPred_eq] at hS ⊢
    rw [hFcnt]
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have hFnn : 0 ≤ F := fun S ↦ Finset.prod_nonneg fun i _ ↦ by
    simp only [hg]; split_ifs <;> norm_num
  have hFm : Measurable F := Finset.measurable_prod _ fun i _ ↦ hgm.comp (measurable_pi_apply i)
  have hFint : Integrable F ν := by
    refine (integrable_const (1 : ℝ)).mono' hFm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun S ↦ ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hFnn S), hFcnt]
    exact pow_le_one₀ (by norm_num) (by norm_num)
  have hmarkov := mul_meas_ge_le_integral_of_nonneg (Filter.Eventually.of_forall hFnn) hFint c
  rw [hEF] at hmarkov
  -- real bound
  have hcpos : 0 < c := by positivity
  have hkey : (1 - p / 2) ^ m ≤ c * (1 / 2) := by
    have h1 : 1 - p / 2 ≤ Real.exp (-(p / 2)) := by
      have := Real.add_one_le_exp (-(p / 2)); linarith
    have h2 : (1 - p / 2) ^ m ≤ Real.exp (-(p / 2)) ^ m :=
      pow_le_pow_left₀ (by linarith) h1 m
    rw [← Real.exp_nat_mul (-(p / 2)) m] at h2
    have hhalf : (1 / 2 : ℝ) = Real.exp (-Real.log 2) := by
      rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
    have hc' : c * (1 / 2) = Real.exp (r * (-Real.log 2)) := by
      rw [hc, ← pow_succ, Nat.sub_add_cancel hr0, hhalf, Real.exp_nat_mul]
    rw [hc']
    refine h2.trans (Real.exp_le_exp.2 ?_)
    have hrlt : (r : ℝ) < ε * m / 2 + 1 := Nat.ceil_lt_add_one (by positivity)
    have hl2 := Real.log_two_lt_d9
    have hl2' := Real.log_two_gt_d9
    have hpm : ε * m ≤ p * m := mul_le_mul_of_nonneg_right hεp.le (Nat.cast_nonneg m)
    have : (r : ℝ) * Real.log 2 ≤ (ε * m / 2 + 1) * Real.log 2 :=
      mul_le_mul_of_nonneg_right hrlt.le (by positivity)
    nlinarith
  have hreal : ν.real {S | c ≤ F S} ≤ 1 / 2 := by
    have := hmarkov.trans hkey
    exact le_of_mul_le_mul_left this hcpos
  calc ν {S | cnt E S < r} ≤ ν {S | c ≤ F S} := measure_mono hsub
    _ = ENNReal.ofReal (ν.real {S | c ≤ F S}) := (ofReal_measureReal (measure_ne_top _ _)).symm
    _ ≤ ENNReal.ofReal (1 / 2) := ENNReal.ofReal_le_ofReal hreal
    _ = 1 / 2 := by rw [ENNReal.ofReal_div_of_pos two_pos]; simp

lemma ghost_bound (μ : Measure Z) [IsProbabilityMeasure μ] {J : Type*} [Countable J]
    (E : J → Set Z) (hE : ∀ j, MeasurableSet (E j)) {ε : ℝ} (hε : 0 < ε) (m : ℕ)
    (hm : 8 ≤ ε * m) :
    iidLaw μ m {S | ∃ j, (∀ i, S i ∉ E j) ∧ ENNReal.ofReal ε < μ (E j)} ≤
      2 * iidLaw (μ.prod μ) m
        {w | ∃ j, (∀ i, (w i).1 ∉ E j) ∧ ⌈ε * m / 2⌉₊ ≤ cnt (E j) (fun i ↦ (w i).2)} := by
  set r := ⌈ε * m / 2⌉₊ with hr
  set ν := iidLaw μ m with hν
  have : IsProbabilityMeasure ν := by rw [hν, iidLaw]; infer_instance
  set B' : Set ((Fin m → Z) × (Fin m → Z)) :=
    {p | ∃ j, (∀ i, p.1 i ∉ E j) ∧ r ≤ cnt (E j) p.2} with hB'
  have hB'm : MeasurableSet B' := by
    have : B' = ⋃ j, ((⋂ i, {p : (Fin m → Z) × (Fin m → Z) | p.1 i ∉ E j}) ∩
        {p | r ≤ cnt (E j) p.2}) := by
      ext p; simp [hB']
    rw [this]
    refine MeasurableSet.iUnion fun j ↦ (MeasurableSet.iInter fun i ↦ ?_).inter ?_
    · exact ((hE j).preimage ((measurable_pi_apply i).comp measurable_fst)).compl
    · exact measurableSet_le measurable_const ((measurable_cnt (hE j)).comp measurable_snd)
  have htrans : (ν.prod ν) B' = iidLaw (μ.prod μ) m
      {w | ∃ j, (∀ i, (w i).1 ∉ E j) ∧ r ≤ cnt (E j) (fun i ↦ (w i).2)} := by
    have hmp := measurePreserving_arrowProdEquivProdArrow Z Z (Fin m)
      (fun _ ↦ μ) (fun _ ↦ μ)
    rw [hν, iidLaw, iidLaw, ← hmp.measure_preimage hB'm.nullMeasurableSet]
    rfl
  rw [← htrans]
  have hsec : ∀ S ∈ {S : Fin m → Z | ∃ j, (∀ i, S i ∉ E j) ∧ ENNReal.ofReal ε < μ (E j)},
      1 / 2 ≤ ν (Prod.mk S ⁻¹' B') := by
    rintro S ⟨j, hj1, hj2⟩
    have hsub : {S' | r ≤ cnt (E j) S'} ⊆ Prod.mk S ⁻¹' B' := fun S' hS' ↦ ⟨j, hj1, hS'⟩
    have hc := chernoff_half μ (hE j) hε hj2 m hm
    have hcompl : ν {S' | r ≤ cnt (E j) S'} = 1 - ν {S' | cnt (E j) S' < r} := by
      rw [← prob_compl_eq_one_sub (measurableSet_lt (measurable_cnt (hE j)) measurable_const)]
      congr 1; ext; simp
    calc (1 / 2 : ENNReal) = 1 - 1 / 2 := by rw [one_div, ENNReal.one_sub_inv_two]
      _ ≤ 1 - ν {S' | cnt (E j) S' < r} := tsub_le_tsub_left hc 1
      _ = _ := hcompl.symm
      _ ≤ _ := measure_mono hsub
  have hlint : (1 / 2 : ENNReal) * ν {S | ∃ j, (∀ i, S i ∉ E j) ∧ ENNReal.ofReal ε < μ (E j)} ≤
      (ν.prod ν) B' := by
    rw [Measure.prod_apply hB'm]
    calc (1 / 2 : ENNReal) * ν {S | ∃ j, (∀ i, S i ∉ E j) ∧ ENNReal.ofReal ε < μ (E j)}
        ≤ (1 / 2) * ν {S | 1 / 2 ≤ ν (Prod.mk S ⁻¹' B')} := by
          gcongr; exact fun h ↦ hsec _ h
      _ ≤ ∫⁻ S, ν (Prod.mk S ⁻¹' B') ∂ν :=
          mul_meas_ge_le_lintegral₀ (measurable_measure_prodMk_left hB'm).aemeasurable _
  calc ν {S | ∃ j, (∀ i, S i ∉ E j) ∧ ENNReal.ofReal ε < μ (E j)}
      = 2 * ((1 / 2) * ν {S | ∃ j, (∀ i, S i ∉ E j) ∧ ENNReal.ofReal ε < μ (E j)}) := by
        rw [← mul_assoc, one_div, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
    _ ≤ 2 * (ν.prod ν) B' := by gcongr

lemma swap_average (μ : Measure Z) [IsProbabilityMeasure μ] {m : ℕ} (B : Set (Fin m → Z × Z))
    (hB : MeasurableSet B) (K : ℕ)
    (hK : ∀ w, (Finset.univ.filter (fun σ : Fin m → Bool ↦ swapAt σ w ∈ B)).card ≤ K) :
    iidLaw (μ.prod μ) m B ≤ (K : ENNReal) / 2 ^ m := by
  set ν := iidLaw (μ.prod μ) m with hν
  have : IsProbabilityMeasure ν := by rw [hν, iidLaw]; infer_instance
  have hmp : ∀ σ : Fin m → Bool, MeasurePreserving (swapAt σ) ν ν := by
    intro σ
    have : swapAt σ = fun w i ↦ (if σ i then (Prod.swap : Z × Z → Z × Z) else id) (w i) := by
      funext w i; simp only [swapAt]; split_ifs <;> rfl
    rw [this, hν, iidLaw]
    refine measurePreserving_pi _ _ fun i ↦ ?_
    split_ifs
    · exact Measure.measurePreserving_swap
    · exact MeasurePreserving.id _
  have hmeas : ∀ σ, MeasurableSet (swapAt σ ⁻¹' B) := fun σ ↦ hB.preimage (hmp σ).measurable
  have hsum : (2 ^ m : ENNReal) * ν B = ∑ σ : Fin m → Bool, ν (swapAt σ ⁻¹' B) := by
    simp_rw [(hmp _).measure_preimage hB.nullMeasurableSet]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fin, nsmul_eq_mul]
    push_cast; ring
  have hint : ∑ σ : Fin m → Bool, ν (swapAt σ ⁻¹' B) =
      ∫⁻ w, ∑ σ : Fin m → Bool, (swapAt σ ⁻¹' B).indicator 1 w ∂ν := by
    rw [lintegral_finsetSum _ (fun σ _ ↦ (measurable_one.indicator (hmeas σ)))]
    refine Finset.sum_congr rfl fun σ _ ↦ ?_
    rw [lintegral_indicator_one (hmeas σ)]
  have hpt : ∀ w, ∑ σ : Fin m → Bool, (swapAt σ ⁻¹' B).indicator (1 : (Fin m → Z × Z) → ENNReal) w ≤ K := by
    intro w
    calc _ = ((Finset.univ.filter (fun σ ↦ swapAt σ w ∈ B)).card : ENNReal) := by
          rw [Finset.card_filter]; push_cast
          refine Finset.sum_congr rfl fun σ _ ↦ ?_
          simp [Set.indicator_apply]
      _ ≤ K := by exact_mod_cast hK w
  have hle : ∫⁻ w, ∑ σ : Fin m → Bool, (swapAt σ ⁻¹' B).indicator 1 w ∂ν ≤ K := by
    calc _ ≤ ∫⁻ _, (K : ENNReal) ∂ν := lintegral_mono hpt
      _ = K := by simp
  rw [ENNReal.le_div_iff_mul_le (by simp) (by simp), mul_comm, hsum, hint]
  exact hle


end Prob

section Hyp

variable {X : Type*} {Y : Type*}

lemma lossMulti_nonneg (h : X → Y) (z : X × Y) : 0 ≤ lossMulti h z := by
  unfold lossMulti; split_ifs <;> simp

lemma lossMulti_of_eq {h : X → Y} {z : X × Y} (hz : h z.1 = z.2) : lossMulti h z = 0 := by
  unfold lossMulti; simp [hz]

lemma lossMulti_of_ne {h : X → Y} {z : X × Y} (hz : h z.1 ≠ z.2) : lossMulti h z = 1 := by
  unfold lossMulti; simp [hz]

/-- The error region of a hypothesis. -/
def errSet (h : X → Y) : Set (X × Y) := {z | h z.1 ≠ z.2}

lemma ndim_le_card [Fintype X] (H : Set (X → Y)) : ndim H ≤ Fintype.card X := by
  unfold ndim; refine iSup₂_le fun C _ ↦ ?_; exact_mod_cast Finset.card_le_univ C

lemma ndim_restrict_le (H : Set (X → Y)) (P : Finset X) :
    ndim ((fun h (x : P) ↦ h x.1) '' H) ≤ ndim H := by
  unfold ndim
  refine iSup₂_le fun C hC ↦ ?_
  obtain ⟨f₀, f₁, hf, hsh⟩ := hC
  rcases C.eq_empty_or_nonempty with rfl | ⟨c, hc⟩
  · simp
  let y₀ := f₀ c
  let g₀ : X → Y := fun x ↦ if hx : x ∈ P then f₀ ⟨x, hx⟩ else y₀
  let g₁ : X → Y := fun x ↦ if hx : x ∈ P then f₁ ⟨x, hx⟩ else y₀
  have hC' : NShatters H (C.map (Function.Embedding.subtype _)) := by
    refine ⟨g₀, g₁, ?_, ?_⟩
    · intro x hx
      obtain ⟨x', hx', rfl⟩ := Finset.mem_map.1 hx
      simp only [g₀, g₁, Function.Embedding.coe_subtype, x'.2, dif_pos]
      exact hf x' hx'
    · intro B hB
      obtain ⟨ρ, ⟨h, hH, rfl⟩, h0, h1⟩ :=
        hsh (C.filter (fun x ↦ x.1 ∈ B)) (Finset.filter_subset _ _)
      refine ⟨h, hH, ?_, ?_⟩
      · intro x hxB
        obtain ⟨x', hx', rfl⟩ := Finset.mem_map.1 (hB hxB)
        have := h0 x' (Finset.mem_filter.2 ⟨hx', hxB⟩)
        simp only [g₀, Function.Embedding.coe_subtype, x'.2, dif_pos]
        exact this
      · intro x hx hxB
        obtain ⟨x', hx', rfl⟩ := Finset.mem_map.1 hx
        have := h1 x' hx' (fun h ↦ hxB (Finset.mem_filter.1 h).2)
        simp only [g₁, Function.Embedding.coe_subtype, x'.2, dif_pos]
        exact this
  have := le_iSup₂ (f := fun (C : Finset X) (_ : NShatters H C) ↦ (C.card : ℕ∞)) _ hC'
  simpa using this

lemma pattern_card_le [Fintype Y] (H : Set (X → Y)) (d : ℕ) (hd : ndim H = d) (G : Set (X → Y))
    (hG : G ⊆ H) {m : ℕ} (hm : 1 ≤ m) (w : Fin m → (X × Y) × (X × Y)) :
    (Set.range (fun (j : G) i ↦
      (decide ((w i).1 ∈ errSet j.1), decide ((w i).2 ∈ errSet j.1)))).ncard ≤
      (2 * m) ^ d * Fintype.card Y ^ (2 * d) := by
  set P : Finset X := Finset.univ.image (fun i ↦ (w i).1.1) ∪
    Finset.univ.image (fun i ↦ (w i).2.1) with hP
  have hmem1 : ∀ i, (w i).1.1 ∈ P := fun i ↦
    Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  have hmem2 : ∀ i, (w i).2.1 ∈ P := fun i ↦
    Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  set R : Set (P → Y) := (fun h (x : P) ↦ h x.1) '' H with hR
  set Φ : (P → Y) → (Fin m → Bool × Bool) := fun ρ i ↦
    (decide (ρ ⟨_, hmem1 i⟩ ≠ (w i).1.2), decide (ρ ⟨_, hmem2 i⟩ ≠ (w i).2.2)) with hΦ
  have hsub : Set.range (fun (j : G) i ↦
      (decide ((w i).1 ∈ errSet j.1), decide ((w i).2 ∈ errSet j.1))) ⊆ Φ '' R := by
    rintro _ ⟨j, rfl⟩
    refine ⟨fun x ↦ j.1 x.1, ⟨j.1, hG j.2, rfl⟩, ?_⟩
    funext i
    simp only [hΦ, Prod.mk.injEq]
    exact ⟨decide_eq_decide.2 Iff.rfl, decide_eq_decide.2 Iff.rfl⟩
  have h1 : ndim R ≤ Fintype.card P := ndim_le_card R
  have h2 : ndim R ≤ d := hd ▸ ndim_restrict_le H P
  obtain ⟨d', hd'⟩ : ∃ d' : ℕ, ndim R = d' :=
    ⟨(ndim R).toNat, (ENat.natCast_toNat (ne_top_of_le_ne_top (ENat.natCast_ne_top _) h1)).symm⟩
  have hd'd : d' ≤ d := by rw [hd'] at h2; exact_mod_cast h2
  have hnat := natarajan_lemma R d' hd'
  have hP1 : 1 ≤ Fintype.card P := by
    rw [Fintype.card_coe]; exact Finset.card_pos.2 ⟨_, hmem1 ⟨0, hm⟩⟩
  have hP2 : Fintype.card P ≤ 2 * m := by
    rw [Fintype.card_coe]
    refine (Finset.card_union_le _ _).trans ?_
    have e1 := Finset.card_image_le (s := Finset.univ) (f := fun i : Fin m ↦ (w i).1.1)
    have e2 := Finset.card_image_le (s := Finset.univ) (f := fun i : Fin m ↦ (w i).2.1)
    simp only [Finset.card_univ, Fintype.card_fin] at e1 e2
    omega
  have hY1 : 1 ≤ Fintype.card Y := Fintype.card_pos_iff.2 ⟨(w ⟨0, hm⟩).1.2⟩
  calc _ ≤ (Φ '' R).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ R.ncard := Set.ncard_image_le (Set.toFinite _)
    _ ≤ _ := hnat
    _ ≤ (2 * m) ^ d * Fintype.card Y ^ (2 * d) :=
      Nat.mul_le_mul ((Nat.pow_le_pow_right hP1 hd'd).trans (Nat.pow_le_pow_left hP2 d))
        (Nat.pow_le_pow_right hY1 (by omega))

lemma eq_of_ndim_zero (H : Set (X → Y)) (hd : ndim H = 0) {h₁ h₂ : X → Y} (h₁H : h₁ ∈ H)
    (h₂H : h₂ ∈ H) : h₁ = h₂ := by
  by_contra hne
  obtain ⟨x, hx⟩ := Function.ne_iff.1 hne
  have hsh : NShatters H {x} := by
    refine ⟨h₁, h₂, fun y hy ↦ by rw [Finset.mem_singleton.1 hy]; exact hx, fun B hB ↦ ?_⟩
    by_cases hxB : x ∈ B
    · refine ⟨h₁, h₁H, fun _ _ ↦ rfl, fun y hy hyB ↦ ?_⟩
      rw [Finset.mem_singleton.1 hy] at hyB; exact absurd hxB hyB
    · refine ⟨h₂, h₂H, fun y hy ↦ ?_, fun _ _ _ ↦ rfl⟩
      have := hB hy; rw [Finset.mem_singleton.1 this] at hy; exact absurd hy hxB
  have := le_iSup₂ (f := fun (C : Finset X) (_ : NShatters H C) ↦ (C.card : ℕ∞)) {x} hsh
  change _ ≤ ndim H at this
  rw [hd] at this; simp at this

lemma two_le_card_of_ndim [Fintype Y] (H : Set (X → Y)) (d : ℕ) (hd : ndim H = d)
    (hd1 : 1 ≤ d) : 2 ≤ Fintype.card Y := by
  by_contra hlt
  push Not at hlt
  have hsub : Subsingleton Y := Fintype.card_le_one_iff_subsingleton.1 (by omega)
  have h0 : ndim H = 0 := by
    unfold ndim
    refine le_antisymm (iSup₂_le fun C hC ↦ ?_) bot_le
    obtain ⟨f₀, f₁, hf, -⟩ := hC
    rcases C.eq_empty_or_nonempty with rfl | ⟨c, hc⟩
    · simp
    · exact absurd (Subsingleton.elim _ _) (hf c hc)
  rw [hd] at h0; norm_cast at h0; omega


end Hyp

lemma final_arith {d k : ℕ} (hd : 1 ≤ d) (hk : 2 ≤ k) {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hδ : 0 < δ) (hδ1 : δ < 1) {m : ℕ}
    (hm : 64 * (d * Real.log (k * d / ε) + Real.log (1 / δ)) / ε ≤ m) :
    8 ≤ ε * m ∧ 2 * ((2 * m : ℝ) ^ d * (k : ℝ) ^ (2 * d)) ≤ δ * 2 ^ ⌈ε * m / 2⌉₊ := by
  set L := Real.log (k * d / ε) with hL
  set l := Real.log (1 / δ) with hl
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hkd : (2 : ℝ) < k * d / ε := by
    rw [lt_div_iff₀ hε]; nlinarith
  have hlog2 := Real.log_two_gt_d9
  have hL2 : Real.log 2 < L := Real.log_lt_log (by norm_num) hkd
  have hl0 : 0 < l := by
    rw [hl]; apply Real.log_pos; rw [lt_div_iff₀ hδ]; linarith
  have hεm : 64 * (d * L + l) ≤ ε * m := by
    rw [div_le_iff₀ hε] at hm; linarith
  have hdL : L ≤ d * L := by nlinarith
  have h8 : 8 ≤ ε * m := by nlinarith
  refine ⟨h8, ?_⟩
  have hm0 : (0 : ℝ) < m := by nlinarith
  set r := ⌈ε * m / 2⌉₊ with hr
  have hr' : ε * m / 2 ≤ r := Nat.le_ceil _
  -- log(2m) bound
  have hu : 0 < 2 * m * ε / (32 * d) := by positivity
  have hv : 0 < 32 * d / ε := by positivity
  have hlogm : Real.log (2 * m) ≤ (2 * m * ε / (32 * d) - 1) + (5 * Real.log 2 + L) := by
    have e : Real.log (2 * m : ℝ) =
        Real.log (2 * m * ε / (32 * d)) + Real.log (32 * d / ε) := by
      rw [← Real.log_mul hu.ne' hv.ne']; congr 1; field_simp
    rw [e]
    have h1 := Real.log_le_sub_one_of_pos hu
    have h2 : Real.log (32 * d / ε) ≤ 5 * Real.log 2 + L := by
      have e2 : (32 * d / ε : ℝ) = 2 ^ 5 * (d / ε) := by ring
      rw [e2, Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      have : Real.log (d / ε) ≤ L := by
        apply Real.log_le_log (by positivity)
        rw [div_le_div_iff_of_pos_right hε]; nlinarith
      push_cast; linarith
    linarith
  have hdlogm : d * Real.log (2 * m) ≤ ε * m / 16 + 5 * d * Real.log 2 + d * L := by
    have := mul_le_mul_of_nonneg_left hlogm (by positivity : (0:ℝ) ≤ d)
    have e : (d : ℝ) * (2 * m * ε / (32 * d) - 1 + (5 * Real.log 2 + L)) =
        ε * m / 16 - d + 5 * d * Real.log 2 + d * L := by field_simp; ring
    rw [e] at this; linarith
  have hlogk : Real.log k ≤ L := by
    apply Real.log_le_log (by positivity)
    rw [le_div_iff₀ hε]; nlinarith
  have hdlogk : d * Real.log k ≤ d * L := mul_le_mul_of_nonneg_left hlogk (by positivity)
  have hd2 : d * Real.log 2 ≤ d * L := mul_le_mul_of_nonneg_left hL2.le (by positivity)
  have hrlog : ε * m / 2 * Real.log 2 ≤ r * Real.log 2 :=
    mul_le_mul_of_nonneg_right hr' (by positivity)
  have hpos : 0 < 2 * ((2 * m : ℝ) ^ d * (k : ℝ) ^ (2 * d)) := by positivity
  rw [← Real.log_le_log_iff hpos (by positivity), Real.log_mul (by norm_num) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
    Real.log_mul hδ.ne' (by positivity), Real.log_pow]
  have hlδ : Real.log δ = -l := by rw [hl, one_div, Real.log_inv]; ring
  rw [hlδ]
  push_cast
  nlinarith


end RealizableUpperAux

open RealizableUpperAux

open Classical in
theorem solution :
    ∃ C₂ : ℝ, 0 < C₂ ∧
      ∀ {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSingletonClass X]
        [MeasurableSpace Y] [MeasurableSingletonClass Y] [Fintype Y]
        (H : Set (X → Y)) (d : ℕ), H.Nonempty → (∀ h ∈ H, Measurable h) →
        NPointwiseSeparable H → ndim H = d →
        ∀ A : Learner (X × Y) (X → Y), IsERMLearner lossMulti H A →
          IsMulticlassPACWith H A (fun ε δ ↦
            ⌈C₂ * (d * Real.log (Fintype.card Y * d / ε) + Real.log (1 / δ)) / ε⌉₊) := by
  refine ⟨64, by norm_num, ?_⟩
  intro X Y _ _ _ _ _ H d hne hmeas hsep hdim A hA ε δ hε hε1 hδ hδ1 D hD f hf hreal m hm
  obtain ⟨hs, hsH, hs0⟩ := hreal
  have hAH : ∀ m S, A m S ∈ H := fun m S ↦ (hA m S).1
  rcases Nat.eq_zero_or_pos d with rfl | hd1
  · have hempty : {S : Fin m → X × Y | ENNReal.ofReal ε < D {x | A m S x ≠ f x}} = ∅ := by
      ext S
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      rw [eq_of_ndim_zero H (by exact_mod_cast hdim) (hAH m S) hsH, hs0]; exact bot_le
    rw [hempty, measure_empty]; exact bot_le
  set k := Fintype.card Y with hk
  have hk2 : 2 ≤ k := two_le_card_of_ndim H d hdim hd1
  have hm' : 64 * (d * Real.log (k * d / ε) + Real.log (1 / δ)) / ε ≤ m :=
    (Nat.le_ceil _).trans (by exact_mod_cast hm)
  obtain ⟨h8, harith⟩ := final_arith hd1 hk2 hε hε1 hδ hδ1 hm'
  have hm1 : 1 ≤ m := by
    have : (0:ℝ) < m := by nlinarith
    exact_mod_cast this
  set g : X → X × Y := fun x ↦ (x, f x) with hg
  have hgm : Measurable g := measurable_id.prodMk hf
  set μ := D.map g with hμ
  have : IsProbabilityMeasure μ := Measure.isProbabilityMeasure_map hgm.aemeasurable
  have herrm : ∀ h : X → Y, Measurable h → MeasurableSet (errSet h) := by
    intro h hh
    have : errSet h = (⋃ y : Y, (h ⁻¹' {y}) ×ˢ {y})ᶜ := by
      ext z
      simp only [errSet, Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_iUnion, Set.mem_prod,
        Set.mem_preimage, Set.mem_singleton_iff, not_exists, not_and]
      constructor
      · intro hz y h1 h2; exact hz (h1.trans h2.symm)
      · intro hz heq; exact hz _ heq rfl
    rw [this]
    exact (MeasurableSet.iUnion fun y ↦
      (hh (measurableSet_singleton y)).prod (measurableSet_singleton y)).compl
  have hμerr : ∀ h : X → Y, Measurable h → μ (errSet h) = D {x | h x ≠ f x} := by
    intro h hh
    rw [hμ, Measure.map_apply hgm (herrm h hh)]; rfl
  obtain ⟨H₀, hH₀H, hH₀c, happrox⟩ := hsep
  have : Countable H₀ := hH₀c.to_subtype
  set E : H₀ → Set (X × Y) := fun j ↦ errSet j.1 with hE
  have hEm : ∀ j, MeasurableSet (E j) := fun j ↦ herrm _ (hmeas _ (hH₀H j.2))
  set r := ⌈ε * m / 2⌉₊ with hr
  set N := {S : Fin m → X × Y | ∃ i, S i ∈ errSet hs} with hN
  set Bad := {S : Fin m → X × Y | ∃ j, (∀ i, S i ∉ E j) ∧ ENNReal.ofReal ε < μ (E j)} with hBad
  have hN0 : iidLaw μ m N = 0 := by
    have : N = ⋃ i, (fun S : Fin m → X × Y ↦ S i) ⁻¹' errSet hs := by ext S; simp [hN]
    rw [this]
    refine measure_iUnion_null fun i ↦ ?_
    refine ((measurePreserving_eval (fun _ : Fin m ↦ μ) i).measure_preimage
      (herrm hs (hmeas hs hsH)).nullMeasurableSet).trans ?_
    rw [hμerr hs (hmeas hs hsH), hs0]
  have hsub : {S : Fin m → X × Y | ENNReal.ofReal ε < D {x | A m S x ≠ f x}} ⊆ N ∪ Bad := by
    intro S hS
    simp only [Set.mem_ofPred_eq] at hS
    by_cases hSN : S ∈ N
    · exact Or.inl hSN
    right
    have hcons_s : ∀ i, hs (S i).1 = (S i).2 := by
      intro i; by_contra hne; exact hSN ⟨i, hne⟩
    have hcons : ∀ i, A m S (S i).1 = (S i).2 := by
      have h1 := (hA m S).2 hs hsH
      have h0 : empRisk lossMulti S hs = 0 := by
        unfold empRisk; rw [Finset.sum_eq_zero fun i _ ↦ lossMulti_of_eq (hcons_s i)]; simp
      rw [h0] at h1
      unfold empRisk at h1
      have hmpos : (0:ℝ) < m := by exact_mod_cast hm1
      have hsum : ∑ i, lossMulti (A m S) (S i) ≤ 0 := by
        rwa [div_le_iff₀ hmpos, zero_mul] at h1
      intro i
      by_contra hne
      have := Finset.single_le_sum (fun j _ ↦ lossMulti_nonneg (A m S) (S j)) (Finset.mem_univ i)
      rw [lossMulti_of_ne hne] at this; linarith
    have hhH := hAH m S
    have hεh : ENNReal.ofReal ε < μ (errSet (A m S)) := by
      rw [hμerr _ (hmeas _ hhH)]; exact hS
    obtain ⟨u, huH₀, hu⟩ := happrox _ hhH
    have hev1 : ∀ᶠ n in Filter.atTop, ∀ i, u n (S i).1 = A m S (S i).1 := by
      rw [Filter.eventually_all]; intro i
      obtain ⟨N, hN⟩ := hu (S i).1
      exact Filter.eventually_atTop.2 ⟨N, hN⟩
    have htend : Filter.Tendsto (fun n ↦ μ (errSet (u n))) Filter.atTop
        (nhds (μ (errSet (A m S)))) := by
      refine tendsto_measure_of_tendsto_indicator Filter.atTop
        (fun n ↦ herrm _ (hmeas _ (hH₀H (huH₀ n)))) MeasurableSet.univ (measure_ne_top _ _)
        (Filter.Eventually.of_forall fun n ↦ Set.subset_univ _) ?_
      intro z
      obtain ⟨N, hN⟩ := hu z.1
      exact Filter.eventually_atTop.2 ⟨N, fun n hn ↦ by simp only [errSet, Set.mem_ofPred_eq, hN n hn]⟩
    have hev2 : ∀ᶠ n in Filter.atTop, ENNReal.ofReal ε < μ (errSet (u n)) :=
      htend.eventually (lt_mem_nhds hεh)
    obtain ⟨n, hn1, hn2⟩ := (hev1.and hev2).exists
    refine ⟨⟨u n, huH₀ n⟩, fun i ↦ ?_, hn2⟩
    show ¬ (u n (S i).1 ≠ (S i).2)
    rw [hn1 i, hcons i]; exact fun h ↦ h rfl
  set B := {w : Fin m → (X × Y) × (X × Y) |
    ∃ j, (∀ i, (w i).1 ∉ E j) ∧ r ≤ cnt (E j) (fun i ↦ (w i).2)} with hB
  have hBm : MeasurableSet B := by
    have : B = ⋃ j, ((⋂ i, {w : Fin m → (X × Y) × (X × Y) | (w i).1 ∉ E j}) ∩
        {w | r ≤ cnt (E j) (fun i ↦ (w i).2)}) := by
      ext w; simp [hB]
    rw [this]
    refine MeasurableSet.iUnion fun j ↦ (MeasurableSet.iInter fun i ↦ ?_).inter ?_
    · exact ((hEm j).preimage (measurable_fst.comp (measurable_pi_apply i))).compl
    · exact measurableSet_le measurable_const ((measurable_cnt (hEm j)).comp
        (measurable_pi_lambda _ fun i ↦ measurable_snd.comp (measurable_pi_apply i)))
  set τ := (2 * m) ^ d * k ^ (2 * d) with hτ
  have hK : ∀ w, (Finset.univ.filter (fun σ : Fin m → Bool ↦ swapAt σ w ∈ B)).card ≤
      τ * 2 ^ (m - r) := by
    intro w
    refine (swap_count w E r).trans (Nat.mul_le_mul_right _ ?_)
    exact pattern_card_le H d hdim H₀ hH₀H hm1 w
  have hrm : r ≤ m := by
    rw [hr, Nat.ceil_le]
    have : (0:ℝ) ≤ m := Nat.cast_nonneg _
    nlinarith
  calc iidLaw μ m {S | ENNReal.ofReal ε < D {x | A m S x ≠ f x}}
      ≤ iidLaw μ m (N ∪ Bad) := measure_mono hsub
    _ ≤ iidLaw μ m N + iidLaw μ m Bad := measure_union_le _ _
    _ = iidLaw μ m Bad := by rw [hN0, zero_add]
    _ ≤ 2 * iidLaw (μ.prod μ) m B := ghost_bound μ E hEm hε m h8
    _ ≤ 2 * (((τ * 2 ^ (m - r) : ℕ) : ENNReal) / 2 ^ m) := by
        gcongr; exact swap_average μ B hBm _ hK
    _ ≤ ENNReal.ofReal δ := by
        have h2m : (2 : ENNReal) ^ m = 2 ^ r * 2 ^ (m - r) := by
          rw [← pow_add, Nat.add_sub_cancel' hrm]
        rw [h2m, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
          ENNReal.mul_div_mul_right _ _ (by positivity) (by simp), ← mul_div_assoc]
        refine ENNReal.div_le_of_le_mul ?_
        have e1 : (2 : ENNReal) * (τ : ENNReal) =
            ENNReal.ofReal (2 * ((2 * m : ℝ) ^ d * (k : ℝ) ^ (2 * d))) := by
          rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_ofNat 2,
            ← ENNReal.ofReal_mul (by norm_num)]
          congr 1; rw [hτ]; push_cast; ring
        have e2 : ENNReal.ofReal δ * 2 ^ r = ENNReal.ofReal (δ * 2 ^ r) := by
          rw [ENNReal.ofReal_mul hδ.le, ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
        rw [e1, e2]
        exact ENNReal.ofReal_le_ofReal harith
