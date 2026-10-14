-- Prove2me | solution 1 for OptimalPAC.SampleComplexity.consistent_error_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:57:07.488984+00:00
-- url     : https://prove2.me/submissions/3aaef318-f62b-43ff-a77d-09bdeaff72fe

import Mathlib
import Definitions.Def_ComputationalLearning_VC
import Definitions.Def_OptimalPAC_SampleComplexity_Model

set_option autoImplicit false

open MeasureTheory ComputationalLearning in
lemma l4_phi_eq (d n : ℕ) : Phi d n = ∑ k ∈ Finset.range (d + 1), n.choose k := by
  induction n generalizing d with
  | zero =>
    cases d with
    | zero => simp [Phi]
    | succ d => simp [Phi, Finset.sum_range_succ']
  | succ n ih =>
    cases d with
    | zero => simp [Phi]
    | succ d =>
      rw [show Phi (d + 1) (n + 1) = Phi (d + 1) n + Phi d n from rfl, ih, ih,
        Finset.sum_range_succ' (fun k => (n + 1).choose k)]
      simp only [Nat.choose_succ_succ, Finset.sum_add_distrib]
      rw [Finset.sum_range_succ' (fun k => n.choose k) (d + 1)]
      simp only [Nat.choose_zero_right]
      ring

open MeasureTheory ComputationalLearning in
lemma l4_phi_mono {d n n' : ℕ} (h : n ≤ n') : Phi d n ≤ Phi d n' := by
  rw [l4_phi_eq, l4_phi_eq]
  exact Finset.sum_le_sum fun k _ => Nat.choose_le_choose k h

open MeasureTheory ComputationalLearning in
lemma l4_sauer {X : Type*} (H : Set (X → Bool)) (d : ℕ) (hd : vcDim H ≤ d) (T : Finset X) :
    (restrictions H T).ncard ≤ Phi d T.card := by
  classical
  let enc : (T → Bool) → Finset X := fun f => T.filter (fun x => ∃ hx : x ∈ T, f ⟨x, hx⟩ = true)
  have henc : Function.Injective enc := by
    intro f g hfg
    funext x
    have := congrArg (fun s => x.1 ∈ s) hfg
    simp only [enc, Finset.mem_filter, eq_iff_iff] at this
    have hx := x.2
    cases hf : f x <;> cases hg : g x <;> simp_all
  let R : Finset (T → Bool) := Finset.univ.filter (fun f => f ∈ restrictions H T)
  let 𝒜 : Finset (Finset X) := R.image enc
  have hR : (restrictions H T).ncard = R.card := by
    rw [← Set.ncard_coe_finset]
    congr 1; ext f; simp [R]
  have h𝒜 : 𝒜.card = R.card := Finset.card_image_of_injective _ henc
  have hsub : ∀ u ∈ 𝒜, u ⊆ T := by
    intro u hu
    obtain ⟨g, -, rfl⟩ := Finset.mem_image.1 hu
    exact Finset.filter_subset _ _
  have hshat : ∀ s, 𝒜.Shatters s → s ⊆ T ∧ s.card ≤ d := by
    intro s hs
    have hsT : s ⊆ T := by
      obtain ⟨u, hu, hsu⟩ := hs.exists_superset
      exact hsu.trans (hsub u hu)
    refine ⟨hsT, ?_⟩
    have hH : Shatters H s := by
      intro f
      obtain ⟨u, hu, hsu⟩ :=
        hs (Finset.filter_subset (fun x => ∃ hx : x ∈ s, f ⟨x, hx⟩ = true) s)
      obtain ⟨g, hgR, rfl⟩ := Finset.mem_image.1 hu
      obtain ⟨h, hH, hgh⟩ := (Finset.mem_filter.1 hgR).2
      refine ⟨h, hH, fun x => ?_⟩
      have hxT : x.1 ∈ T := hsT x.2
      have key := congrArg (fun t => x.1 ∈ t) hsu
      simp only [enc, Finset.mem_inter, Finset.mem_filter, eq_iff_iff] at key
      have hg := hgh ⟨x.1, hxT⟩
      have hx2 := x.2
      cases hfx : f x <;> cases hgx : g ⟨x.1, hxT⟩ <;> simp_all
    have h1 : (s.card : ℕ∞) ≤ vcDim H :=
      le_iSup₂ (f := fun (S : Finset X) (_ : Shatters H S) => (S.card : ℕ∞)) s hH
    exact_mod_cast h1.trans hd
  calc (restrictions H T).ncard = 𝒜.card := by rw [hR, h𝒜]
    _ ≤ 𝒜.shatterer.card := Finset.card_le_card_shatterer 𝒜
    _ ≤ ∑ k ∈ Finset.range (d + 1), (T.powersetCard k).card := by
        refine (Finset.card_le_card fun s hs => Finset.mem_biUnion.2 ⟨s.card, ?_⟩).trans
          Finset.card_biUnion_le
        have := hshat s (Finset.mem_shatterer.1 hs)
        exact ⟨Finset.mem_range.2 (by omega), Finset.mem_powersetCard.2 ⟨this.1, rfl⟩⟩
    _ = Phi d T.card := by rw [l4_phi_eq]; simp [Finset.card_powersetCard]

open MeasureTheory ComputationalLearning in
/-- Swap the coordinates where `σ` is `true`. -/
def l4_swap {X : Type*} {m : ℕ} (σ : Fin m → Bool) (p : (Fin m → X) × (Fin m → X)) :
    (Fin m → X) × (Fin m → X) :=
  (fun i => if σ i then p.2 i else p.1 i, fun i => if σ i then p.1 i else p.2 i)

open MeasureTheory ComputationalLearning in
lemma l4_swap_mp {X : Type*} [MeasurableSpace X] (D : Measure X) [IsProbabilityMeasure D]
    {m : ℕ} (σ : Fin m → Bool) :
    MeasurePreserving (l4_swap σ)
      ((Measure.pi fun _ : Fin m => D).prod (Measure.pi fun _ : Fin m => D))
      ((Measure.pi fun _ : Fin m => D).prod (Measure.pi fun _ : Fin m => D)) := by
  let E := MeasurableEquiv.arrowProdEquivProdArrow X X (Fin m)
  have hE : MeasurePreserving E (Measure.pi fun _ : Fin m => D.prod D)
      ((Measure.pi fun _ : Fin m => D).prod (Measure.pi fun _ : Fin m => D)) :=
    measurePreserving_arrowProdEquivProdArrow X X (Fin m) (fun _ => D) (fun _ => D)
  let f : Fin m → X × X → X × X := fun i => if σ i then Prod.swap else id
  have hf : ∀ i, MeasurePreserving (f i) (D.prod D) (D.prod D) := by
    intro i
    by_cases h : σ i
    · simp only [f, h, if_true]; exact Measure.measurePreserving_swap
    · simp only [f, h]; exact MeasurePreserving.id _
  have hF := measurePreserving_pi (fun _ : Fin m => D.prod D) (fun _ : Fin m => D.prod D) hf
  have hcomp := hE.comp (hF.comp hE.symm)
  have heq : l4_swap σ = E ∘ ((fun a i => f i (a i)) ∘ E.symm) := by
    funext p
    ext i
    · by_cases h : σ i <;> simp [l4_swap, f, h, E, MeasurableEquiv.arrowProdEquivProdArrow,
        Equiv.arrowProdEquivProdArrow]
    · by_cases h : σ i <;> simp [l4_swap, f, h, E, MeasurableEquiv.arrowProdEquivProdArrow,
        Equiv.arrowProdEquivProdArrow]
  rw [heq]; exact hcomp

open MeasureTheory ComputationalLearning Classical in
lemma l4_count {X : Type*} (H : Set (X → Bool)) (d : ℕ) (hd : vcDim H ≤ d) (c : X → Bool)
    (ε : ℝ) (m : ℕ) (z : (Fin m → X) × (Fin m → X)) :
    ((Finset.univ.filter fun σ : Fin m → Bool =>
        l4_swap σ z ∈ doubleSampleEvent H c ε m).card : ℝ)
      ≤ Phi d (2 * m) * (2 : ℝ) ^ m * (2 : ℝ) ^ (-(ε * m / 2)) := by
  obtain ⟨x, y⟩ := z
  let pat : (X → Bool) → (Fin m → Bool × Bool) := fun h i =>
    (decide (h (x i) ≠ c (x i)), decide (h (y i) ≠ c (y i)))
  let Pats : Finset (Fin m → Bool × Bool) := Finset.univ.filter fun P => ∃ h ∈ H, pat h = P
  let G : (Fin m → Bool × Bool) → Finset (Fin m → Bool) := fun P => Finset.univ.filter fun σ =>
    (∀ i, (if σ i then (P i).2 else (P i).1) = false) ∧
      ε * m / 2 ≤ ((Finset.univ.filter fun i =>
        (if σ i then (P i).1 else (P i).2) = true).card : ℝ)
  -- (A) number of patterns
  have hA : (Pats.card : ℝ) ≤ Phi d (2 * m) := by
    let T : Finset X := Finset.univ.image x ∪ Finset.univ.image y
    have hxT : ∀ i, x i ∈ T := fun i =>
      Finset.mem_union_left _ (Finset.mem_image_of_mem x (Finset.mem_univ i))
    have hyT : ∀ i, y i ∈ T := fun i =>
      Finset.mem_union_right _ (Finset.mem_image_of_mem y (Finset.mem_univ i))
    let Ψ : (T → Bool) → (Fin m → Bool × Bool) := fun f i =>
      (decide (f ⟨x i, hxT i⟩ ≠ c (x i)), decide (f ⟨y i, hyT i⟩ ≠ c (y i)))
    let R : Finset (T → Bool) := Finset.univ.filter (fun f => f ∈ restrictions H T)
    have hsub : Pats ⊆ R.image Ψ := by
      intro P hP
      obtain ⟨h, hH, rfl⟩ := (Finset.mem_filter.1 hP).2
      exact Finset.mem_image.2 ⟨fun t => h t.1,
        Finset.mem_filter.2 ⟨Finset.mem_univ _, h, hH, fun t => rfl⟩, rfl⟩
    have hR : R.card = (restrictions H T).ncard := by
      rw [← Set.ncard_coe_finset]; congr 1; ext f; simp [R]
    have hT : T.card ≤ 2 * m := by
      calc T.card ≤ (Finset.univ.image x).card + (Finset.univ.image y).card :=
            Finset.card_union_le _ _
        _ ≤ m + m := by
          gcongr <;> exact (Finset.card_image_le).trans (by simp)
        _ = 2 * m := by ring
    have h1 : Pats.card ≤ Phi d (2 * m) :=
      calc Pats.card ≤ (R.image Ψ).card := Finset.card_le_card hsub
        _ ≤ R.card := Finset.card_image_le
        _ = (restrictions H T).ncard := hR
        _ ≤ Phi d T.card := l4_sauer H d hd T
        _ ≤ Phi d (2 * m) := l4_phi_mono hT
    exact_mod_cast h1
  -- (B) covering
  have hB : (Finset.univ.filter fun σ : Fin m → Bool =>
      l4_swap σ (x, y) ∈ doubleSampleEvent H c ε m) ⊆ Pats.biUnion G := by
    intro σ hσ
    have hmem := (Finset.mem_filter.1 hσ).2
    simp only [doubleSampleEvent, Set.mem_ofPred_eq] at hmem
    obtain ⟨h, hH, h1, h2⟩ := hmem
    refine Finset.mem_biUnion.2 ⟨pat h, Finset.mem_filter.2 ⟨Finset.mem_univ _, h, hH, rfl⟩, ?_⟩
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, fun i => ?_, ?_⟩
    · have := h1 i
      by_cases hs : σ i <;> simp_all [l4_swap, pat]
    · refine h2.trans (le_of_eq ?_)
      congr 2
      apply Finset.filter_congr
      intro i _
      by_cases hs : σ i <;> simp [l4_swap, pat, hs]
  -- (C) each G P is small
  have hC : ∀ P, ((G P).card : ℝ) ≤ (2 : ℝ) ^ m * (2 : ℝ) ^ (-(ε * m / 2)) := by
    intro P
    rcases (G P).eq_empty_or_nonempty with he | ⟨σ0, hσ0⟩
    · rw [he]; simp only [Finset.card_empty, Nat.cast_zero]; positivity
    let I : Finset (Fin m) := Finset.univ.filter fun i => (P i).1 = true ∨ (P i).2 = true
    have hσ0' := (Finset.mem_filter.1 hσ0).2
    have hIcard : ε * m / 2 ≤ (I.card : ℝ) := by
      refine hσ0'.2.trans ?_
      exact_mod_cast Finset.card_le_card (fun i hi => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, I] at hi ⊢
        by_cases hs : σ0 i <;> simp_all)
    have hdet : ∀ σ ∈ G P, ∀ i ∈ I, σ i = (P i).1 := by
      intro σ hσ i hi
      have h1 := (Finset.mem_filter.1 hσ).2.1 i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, I] at hi
      cases hs : σ i <;> cases hp1 : (P i).1 <;> cases hp2 : (P i).2 <;> simp_all
    have hinj : (G P).card ≤ Fintype.card ({i // i ∉ I} → Bool) := by
      rw [← Finset.card_univ]
      refine Finset.card_le_card_of_injOn (fun σ j => σ j.1) (fun _ _ => Finset.mem_univ _) ?_
      intro σ hσ τ hτ hστ
      funext i
      by_cases hi : i ∈ I
      · rw [hdet σ hσ i hi, hdet τ hτ i hi]
      · exact congrFun hστ ⟨i, hi⟩
    have hcardc : Fintype.card ({i // i ∉ I} → Bool) = 2 ^ (m - I.card) := by
      rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_subtype_compl, Fintype.card_fin,
        Fintype.card_coe]
    have hIm : I.card ≤ m := (Finset.card_le_univ I).trans (by simp)
    have h2pos : (0 : ℝ) < 2 ^ ((I.card : ℕ) : ℝ) := by positivity
    calc ((G P).card : ℝ) ≤ ((2 ^ (m - I.card) : ℕ) : ℝ) := by
          rw [← hcardc]; exact_mod_cast hinj
      _ = (2 : ℝ) ^ m / (2 : ℝ) ^ ((I.card : ℕ) : ℝ) := by
          rw [Real.rpow_natCast]; push_cast
          rw [pow_sub₀ _ (by norm_num) hIm, div_eq_mul_inv]
      _ ≤ (2 : ℝ) ^ m / (2 : ℝ) ^ (ε * m / 2) := by
          apply div_le_div_of_nonneg_left (by positivity) (by positivity)
          exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hIcard
      _ = (2 : ℝ) ^ m * (2 : ℝ) ^ (-(ε * m / 2)) := by
          rw [Real.rpow_neg (by norm_num), div_eq_mul_inv]
  -- (D) combine
  calc ((Finset.univ.filter fun σ : Fin m → Bool =>
        l4_swap σ (x, y) ∈ doubleSampleEvent H c ε m).card : ℝ)
      ≤ ((Pats.biUnion G).card : ℝ) := by exact_mod_cast Finset.card_le_card hB
    _ ≤ ∑ P ∈ Pats, ((G P).card : ℝ) := by exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _P ∈ Pats, (2 : ℝ) ^ m * (2 : ℝ) ^ (-(ε * m / 2)) :=
        Finset.sum_le_sum fun P _ => hC P
    _ = (Pats.card : ℝ) * ((2 : ℝ) ^ m * (2 : ℝ) ^ (-(ε * m / 2))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Phi d (2 * m) : ℝ) * ((2 : ℝ) ^ m * (2 : ℝ) ^ (-(ε * m / 2))) := by
        gcongr
    _ = Phi d (2 * m) * (2 : ℝ) ^ m * (2 : ℝ) ^ (-(ε * m / 2)) := by ring

open MeasureTheory ComputationalLearning Classical in
lemma l4_double_le {X : Type*} [MeasurableSpace X] (H : Set (X → Bool)) (d : ℕ)
    (hd : vcDim H ≤ d) (c : X → Bool) (D : Measure X) [IsProbabilityMeasure D] (ε : ℝ) (m : ℕ)
    (hB : NullMeasurableSet (doubleSampleEvent H c ε m)
      ((Measure.pi fun _ : Fin m ↦ D).prod (Measure.pi fun _ : Fin m ↦ D))) :
    ((Measure.pi fun _ : Fin m ↦ D).prod (Measure.pi fun _ : Fin m ↦ D))
        (doubleSampleEvent H c ε m) ≤
      ENNReal.ofReal (Phi d (2 * m) * (2 : ℝ) ^ (-(ε * m / 2))) := by
  set ν := (Measure.pi fun _ : Fin m ↦ D).prod (Measure.pi fun _ : Fin m ↦ D) with hν
  set B := doubleSampleEvent H c ε m with hBdef
  set K : ℝ := Phi d (2 * m) * (2 : ℝ) ^ (-(ε * m / 2)) with hK
  have hK0 : 0 ≤ K := by positivity
  have hpre : ∀ σ : Fin m → Bool, ν (l4_swap σ ⁻¹' B) = ν B := fun σ =>
    (l4_swap_mp D σ).measure_preimage hB
  have hnull : ∀ σ : Fin m → Bool, NullMeasurableSet (l4_swap σ ⁻¹' B) ν := fun σ =>
    hB.preimage (l4_swap_mp D σ).quasiMeasurePreserving
  have hsum : ∑ σ : Fin m → Bool, ν (l4_swap σ ⁻¹' B) =
      ∫⁻ z, ((Finset.univ.filter fun σ : Fin m → Bool => l4_swap σ z ∈ B).card : ENNReal) ∂ν := by
    have : ∀ σ : Fin m → Bool,
        ν (l4_swap σ ⁻¹' B) = ∫⁻ z, (l4_swap σ ⁻¹' B).indicator 1 z ∂ν :=
      fun σ => (lintegral_indicator_one₀ (hnull σ)).symm
    simp_rw [this]
    rw [← lintegral_finsetSum' Finset.univ
      (f := fun σ z => (l4_swap σ ⁻¹' B).indicator (1 : (Fin m → X) × (Fin m → X) → ENNReal) z)
      (fun σ _ => measurable_one.aemeasurable.indicator₀ (hnull σ))]
    congr 1; funext z
    rw [Finset.card_filter]; push_cast
    refine Finset.sum_congr rfl fun σ _ => ?_
    simp [Set.indicator_apply]
  have hbound : ∀ z, ((Finset.univ.filter fun σ : Fin m → Bool => l4_swap σ z ∈ B).card : ENNReal)
      ≤ ENNReal.ofReal (Phi d (2 * m) * (2 : ℝ) ^ m * (2 : ℝ) ^ (-(ε * m / 2))) := by
    intro z
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (l4_count H d hd c ε m z)
  have h2 : (2 : ENNReal) ^ m * ν B ≤ (2 : ENNReal) ^ m * ENNReal.ofReal K := by
    calc (2 : ENNReal) ^ m * ν B = ∑ σ : Fin m → Bool, ν (l4_swap σ ⁻¹' B) := by
          simp [hpre, Finset.card_univ, Fintype.card_bool]
      _ = ∫⁻ z, ((Finset.univ.filter fun σ : Fin m → Bool =>
            l4_swap σ z ∈ B).card : ENNReal) ∂ν := hsum
      _ ≤ ∫⁻ _z, ENNReal.ofReal (Phi d (2 * m) * (2 : ℝ) ^ m * (2 : ℝ) ^ (-(ε * m / 2))) ∂ν :=
          lintegral_mono hbound
      _ = ENNReal.ofReal (Phi d (2 * m) * (2 : ℝ) ^ m * (2 : ℝ) ^ (-(ε * m / 2))) := by
          rw [lintegral_const, measure_univ, mul_one]
      _ = (2 : ENNReal) ^ m * ENNReal.ofReal K := by
          rw [show (Phi d (2 * m) : ℝ) * (2 : ℝ) ^ m * (2 : ℝ) ^ (-(ε * m / 2)) =
              (2 : ℝ) ^ m * K by rw [hK]; ring,
            ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num)]
          simp
  exact (ENNReal.mul_le_mul_iff_right (by positivity) (by simp)).1 h2


open MeasureTheory ProbabilityTheory ComputationalLearning in
lemma l4_cheb {X : Type*} [MeasurableSpace X] (D : Measure X) [IsProbabilityMeasure D]
    (P : X → Prop) [DecidablePred P] (hE : MeasurableSet {x | P x}) {ε : ℝ} (hε : 0 < ε)
    (m : ℕ) (hm : 8 / ε ≤ m) (hDE : ENNReal.ofReal ε ≤ D {x | P x}) :
    (1 / 2 : ENNReal) ≤ (Measure.pi fun _ : Fin m ↦ D)
      {y | ε * m / 2 ≤ ((Finset.univ.filter fun i => P (y i)).card : ℝ)} := by
  set E : Set X := {x | P x} with hEdef
  set μ : Measure (Fin m → X) := Measure.pi fun _ : Fin m ↦ D with hμ
  set p : ℝ := (D E).toReal with hp
  have hεp : ε ≤ p := (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top D E)).1 hDE
  have hm0 : (8 : ℝ) ≤ ε * m := by
    have := (div_le_iff₀ hε).1 hm
    linarith
  have hp0 : 0 < p := lt_of_lt_of_le hε hεp
  set f : X → ℝ := E.indicator 1 with hf
  have hfm : Measurable f := measurable_one.indicator hE
  have hf01 : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1 := by
    intro x; simp only [hf, Set.indicator_apply, Pi.one_apply]; split_ifs <;> norm_num
  have hfL2 : MemLp f 2 D :=
    MemLp.of_bound hfm.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [(hf01 x).1, (hf01 x).2])
  have hfint : ∫ x, f x ∂D = p := by rw [hf, integral_indicator_one hE]; rfl
  set N : (Fin m → X) → ℝ := ∑ i, fun y : Fin m → X => f (y i) with hN
  have hNapp : ∀ y, N y = ∑ i, f (y i) := fun y => by simp [hN, Finset.sum_apply]
  have hNcard : ∀ y, ((Finset.univ.filter fun i => P (y i)).card : ℝ) = N y := by
    intro y
    rw [hNapp, Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [hf, Set.indicator_apply, hEdef]
  have hNm : Measurable N := by
    have : N = fun y => ∑ i, f (y i) := funext hNapp
    rw [this]; exact Finset.measurable_sum _ (fun i _ => hfm.comp (measurable_pi_apply i))
  have hNL2 : MemLp N 2 μ :=
    MemLp.of_bound hNm.aestronglyMeasurable m (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, hNapp]
      calc |∑ i, f (y i)| ≤ ∑ i, |f (y i)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : Fin m, (1 : ℝ) := Finset.sum_le_sum fun i _ => by
            rw [abs_le]; constructor <;> linarith [(hf01 (y i)).1, (hf01 (y i)).2]
        _ = m := by simp)
  have hmean : μ[N] = m * p := by
    simp_rw [hNapp]
    rw [integral_finsetSum _ (fun i _ => ?_)]
    · rw [Finset.sum_congr rfl fun i _ =>
        integral_comp_eval (μ := fun _ : Fin m => D) (i := i) hfm.aestronglyMeasurable]
      simp [hfint]
    · exact integrable_comp_eval (μ := fun _ : Fin m => D) (hfL2.integrable one_le_two)
  have hvar : Var[N; μ] ≤ m * p := by
    have hv := variance_sum_pi (μ := fun _ : Fin m => D) (X := fun _ => f) (fun _ => hfL2)
    rw [hN, hv]
    have hv1 : Var[f; D] ≤ p := by
      have := variance_le_sub_mul_sub (μ := D) (a := 0) (b := 1)
        (Filter.Eventually.of_forall hf01) hfm.aemeasurable
      rw [hfint] at this
      nlinarith [hp0, this]
    calc ∑ _i : Fin m, Var[f; D] ≤ ∑ _i : Fin m, p := Finset.sum_le_sum fun _ _ => hv1
      _ = m * p := by simp
  have hmpos : (0 : ℝ) < m := by
    by_contra h0
    have h0' := not_lt.1 h0
    nlinarith
  set cc : ℝ := m * p / 2 with hcc
  have hc : 0 < cc := by positivity
  have hcheb := meas_ge_le_variance_div_sq hNL2 hc
  set S : Set (Fin m → X) :=
    {y | ε * m / 2 ≤ ((Finset.univ.filter fun i => P (y i)).card : ℝ)} with hSdef
  have hsub : Sᶜ ⊆ {ω | cc ≤ |N ω - μ[N]|} := by
    intro y hy
    simp only [hSdef, Set.mem_compl_iff, Set.mem_ofPred_eq, not_le, hNcard] at hy ⊢
    rw [hmean]
    have : ε * m ≤ p * m := mul_le_mul_of_nonneg_right hεp (Nat.cast_nonneg m)
    rw [le_abs]; right; rw [hcc]; linarith
  have hbound : ENNReal.ofReal (Var[N; μ] / cc ^ 2) ≤ 1 / 2 := by
    rw [show (1 / 2 : ENNReal) = ENNReal.ofReal (1 / 2) by
      rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp]
    apply ENNReal.ofReal_le_ofReal
    rw [div_le_iff₀ (by positivity)]
    have hmp : 8 ≤ (m : ℝ) * p := by nlinarith
    rw [hcc]
    nlinarith
  have hS : MeasurableSet S := by
    have : S = {y | ε * m / 2 ≤ N y} := by
      ext y; simp only [hSdef, Set.mem_ofPred_eq, hNcard]
    rw [this]; exact measurableSet_le measurable_const hNm
  have hcompl : μ Sᶜ ≤ 1 / 2 := (measure_mono hsub).trans (hcheb.trans hbound)
  have htot := measure_add_measure_compl (μ := μ) hS
  rw [measure_univ] at htot
  have h1 : μ S + μ Sᶜ ≤ μ S + 1 / 2 := add_le_add le_rfl hcompl
  rw [htot] at h1
  have h1' : (1 / 2 : ENNReal) + 1 / 2 ≤ μ S + 1 / 2 := by
    rw [ENNReal.add_halves]; exact h1
  exact ENNReal.le_of_add_le_add_right (by simp) h1'


open MeasureTheory ComputationalLearning in
lemma l4_step1 {X : Type*} [MeasurableSpace X] (H : Set (X → Bool))
    (hHm : ∀ h ∈ H, Measurable h) (c : X → Bool) (hc : Measurable c)
    (D : Measure X) [IsProbabilityMeasure D] {ε : ℝ} (hε : 0 < ε) (m : ℕ) (hm : 8 / ε ≤ m) :
    ∃ M : Set (Fin m → X), MeasurableSet M ∧
      {x : Fin m → X | ∃ h ∈ H, ENNReal.ofReal ε ≤ D (errorRegion c h) ∧
        ∀ i, x i ∉ errorRegion c h} ⊆ M ∧
      (Measure.pi fun _ : Fin m ↦ D) M ≤
        2 * ((Measure.pi fun _ : Fin m ↦ D).prod (Measure.pi fun _ : Fin m ↦ D))
          (doubleSampleEvent H c ε m) := by
  set μ : Measure (Fin m → X) := Measure.pi fun _ : Fin m ↦ D with hμ
  set B := doubleSampleEvent H c ε m with hB
  set B' := toMeasurable (μ.prod μ) B with hB'
  have hB'm : MeasurableSet B' := measurableSet_toMeasurable _ _
  set g : (Fin m → X) → ENNReal := fun x => μ (Prod.mk x ⁻¹' B') with hg
  have hgm : Measurable g := measurable_measure_prodMk_left hB'm
  refine ⟨{x | 1 / 2 ≤ g x}, measurableSet_le measurable_const hgm, ?_, ?_⟩
  · rintro x ⟨h, hH, hDh, hx⟩
    simp only [Set.mem_ofPred_eq]
    have hsub : {y : Fin m → X | ε * m / 2 ≤
        ((Finset.univ.filter fun i => h (y i) ≠ c (y i)).card : ℝ)} ⊆ Prod.mk x ⁻¹' B' := by
      intro y hy
      have hxy : (x, y) ∈ B := by
        refine ⟨h, hH, fun i => ?_, hy⟩
        simpa [errorRegion] using hx i
      exact subset_toMeasurable _ _ hxy
    refine le_trans ?_ (measure_mono hsub)
    exact l4_cheb D (fun x => h x ≠ c x) (measurableSet_eq_fun (hHm h hH) hc).compl hε m hm hDh
  · have hmark := mul_meas_ge_le_lintegral₀ (μ := μ) hgm.aemeasurable (1 / 2 : ENNReal)
    have hint : ∫⁻ x, g x ∂μ = (μ.prod μ) B := by
      rw [hg, ← Measure.prod_apply hB'm, hB', measure_toMeasurable]
    rw [hint] at hmark
    have h2 : (2 : ENNReal) * (1 / 2) = 1 := by
      rw [one_div, ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]
    calc μ {x | 1 / 2 ≤ g x} = 2 * ((1 / 2) * μ {x | 1 / 2 ≤ g x}) := by
          rw [← mul_assoc, h2, one_mul]
      _ ≤ 2 * (μ.prod μ) B := by gcongr

open MeasureTheory ComputationalLearning in
lemma l4_phi_exp (d n : ℕ) (hd : 1 ≤ d) (hdn : d ≤ n) :
    (Phi d n : ℝ) ≤ (Real.exp 1 * n / d) ^ d := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le hd hdn)
  set x : ℝ := d / n with hx
  have hx0 : 0 < x := by positivity
  have hx1 : x ≤ 1 := by rw [hx, div_le_one hnpos]; exact_mod_cast hdn
  have hmain : (Phi d n : ℝ) * x ^ d ≤ Real.exp 1 ^ d := by
    rw [l4_phi_eq, Nat.cast_sum, Finset.sum_mul]
    calc ∑ k ∈ Finset.range (d + 1), ((n.choose k : ℕ) : ℝ) * x ^ d
        ≤ ∑ k ∈ Finset.range (d + 1), (n.choose k : ℝ) * x ^ k := by
          apply Finset.sum_le_sum; intro k hk
          have hk' : k ≤ d := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
          exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hx0.le hx1 hk') (by positivity)
      _ ≤ ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * x ^ k := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · exact Finset.range_subset_range.2 (by omega)
          · intros; positivity
      _ = (x + 1) ^ n := by
          rw [add_pow]; apply Finset.sum_congr rfl; intros; rw [one_pow]; ring
      _ ≤ Real.exp x ^ n := by
          gcongr; linarith [Real.add_one_le_exp x]
      _ = Real.exp 1 ^ d := by
          rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]; congr 1; rw [hx]; field_simp
  have : (Real.exp 1 * n / d) ^ d = Real.exp 1 ^ d / x ^ d := by
    rw [hx, div_pow, div_pow, mul_pow]; field_simp
  rw [this, le_div_iff₀ (by positivity)]
  exact hmain

open MeasureTheory ComputationalLearning in
lemma l4_core {X : Type*} [MeasurableSpace X] (H : Set (X → Bool))
    (hHm : ∀ h ∈ H, Measurable h) (d : ℕ) (hd : vcDim H ≤ d) (c : X → Bool) (hc : Measurable c)
    (hwb : IsWellBehaved H c)
    (D : Measure X) [IsProbabilityMeasure D] {ε : ℝ} (hε : 0 < ε) (m : ℕ) (hm : 8 / ε ≤ m) :
    ∃ M : Set (Fin m → X), MeasurableSet M ∧
      {x : Fin m → X | ∃ h ∈ H, ENNReal.ofReal ε ≤ D (errorRegion c h) ∧
        ∀ i, x i ∉ errorRegion c h} ⊆ M ∧
      (Measure.pi fun _ : Fin m ↦ D) M ≤
        ENNReal.ofReal (2 * Phi d (2 * m) * (2 : ℝ) ^ (-(ε * m / 2))) := by
  obtain ⟨M, hM, hAM, hμM⟩ := l4_step1 H hHm c hc D hε m hm
  refine ⟨M, hM, hAM, hμM.trans ?_⟩
  have h2 := l4_double_le H d hd c D ε m (hwb D inferInstance ε m)
  calc 2 * ((Measure.pi fun _ : Fin m ↦ D).prod (Measure.pi fun _ : Fin m ↦ D))
          (doubleSampleEvent H c ε m)
      ≤ 2 * ENNReal.ofReal (Phi d (2 * m) * (2 : ℝ) ^ (-(ε * m / 2))) := by gcongr
    _ = ENNReal.ofReal (2 * Phi d (2 * m) * (2 : ℝ) ^ (-(ε * m / 2))) := by
        rw [show (2 : ℝ) * Phi d (2 * m) * (2 : ℝ) ^ (-(ε * m / 2)) =
            2 * (Phi d (2 * m) * (2 : ℝ) ^ (-(ε * m / 2))) by ring,
          ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 by norm_num), ENNReal.ofReal_ofNat]

lemma l4_vc_le {X : Type*} (C : Set (X → Bool)) (d : ℕ)
    (hd : OptimalPAC.SampleComplexity.vcDim C = d) : ComputationalLearning.vcDim C ≤ d := by
  rw [← hd]
  unfold ComputationalLearning.vcDim
  refine iSup₂_le fun S hS => ?_
  let x : Fin S.card → X := fun i => (S.equivFin.symm i).1
  have hx : OptimalPAC.SampleComplexity.Shatters C x := by
    intro y
    obtain ⟨c, hc, hcy⟩ := hS (fun s => y (S.equivFin s))
    exact ⟨c, hc, fun i => by simpa [x] using hcy (S.equivFin.symm i)⟩
  exact le_iSup₂ (f := fun (k : ℕ) (_ : ∃ x : Fin k → X,
    OptimalPAC.SampleComplexity.Shatters C x) => (k : ℕ∞)) S.card ⟨x, hx⟩

lemma l4_d_pos {X : Type*} (C : Set (X → Bool)) (hC3 : 3 ≤ C.encard) (d : ℕ)
    (hd : OptimalPAC.SampleComplexity.vcDim C = d) : 1 ≤ d := by
  have h1 : 1 < C.encard := lt_of_lt_of_le (by norm_num) hC3
  obtain ⟨a, b, ha, hb, hab⟩ := Set.one_lt_encard_iff.1 h1
  obtain ⟨x, hx⟩ : ∃ x, a x ≠ b x := by
    by_contra h; push_neg at h; exact hab (funext h)
  have hS : OptimalPAC.SampleComplexity.Shatters C (fun _ : Fin 1 => x) := by
    intro y
    by_cases hy : a x = y 0
    · exact ⟨a, ha, fun i => by fin_cases i; simpa using hy⟩
    · refine ⟨b, hb, fun i => ?_⟩
      fin_cases i
      have : b x = y 0 := by
        cases hax : a x <;> cases hbx : b x <;> cases hy0 : y 0 <;> simp_all
      simpa using this
  have : ((1 : ℕ) : ℕ∞) ≤ OptimalPAC.SampleComplexity.vcDim C :=
    le_iSup₂ (f := fun (k : ℕ) (_ : ∃ x : Fin k → X,
      OptimalPAC.SampleComplexity.Shatters C x) => (k : ℕ∞)) 1 ⟨_, hS⟩
  rw [hd] at this; exact_mod_cast this

lemma l4_dse_eq {X : Type*} (C : Set (X → Bool)) (f : X → Bool) (t : ℝ) (m : ℕ) :
    OptimalPAC.SampleComplexity.doubleSampleEvent C f t m =
      ComputationalLearning.doubleSampleEvent C f t m := by
  ext p
  simp only [OptimalPAC.SampleComplexity.doubleSampleEvent,
    ComputationalLearning.doubleSampleEvent, Set.mem_setOf_eq]
  have : ∀ h : X → Bool, ({i : Fin m | h (p.2 i) ≠ f (p.2 i)}.ncard : ℝ) =
      ((Finset.univ.filter fun i => h (p.2 i) ≠ f (p.2 i)).card : ℝ) := by
    intro h
    rw [← Set.ncard_coe_finset, Finset.coe_filter]; simp
  simp_rw [this]

lemma l4_wb {X : Type*} [MeasurableSpace X] (C : Set (X → Bool))
    (hWB : OptimalPAC.SampleComplexity.WellBehaved C) (f : X → Bool) (hf : f ∈ C) :
    ComputationalLearning.IsWellBehaved C f := by
  intro D hD ε m
  rw [← l4_dse_eq]; exact (hWB f hf D hD m ε).2

lemma l4_phi_le_two_pow (d n : ℕ) : (ComputationalLearning.Phi d n : ℝ) ≤ 2 ^ n := by
  have : ComputationalLearning.Phi d n ≤ 2 ^ n := by
    rw [l4_phi_eq]
    calc ∑ k ∈ Finset.range (d + 1), n.choose k
        ≤ ∑ k ∈ Finset.range (n + d + 1), n.choose k :=
          Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 (by omega))
      _ = ∑ k ∈ Finset.range (n + 1), n.choose k := by
          refine (Finset.sum_subset (Finset.range_subset_range.2 (by omega)) ?_).symm
          intro k _ hk
          simp only [Finset.mem_range, not_lt] at hk
          exact Nat.choose_eq_zero_of_lt (by omega)
      _ = 2 ^ n := Nat.sum_range_choose n
  exact_mod_cast this

lemma l4_Log2_ge (z : ℝ) : 1 ≤ OptimalPAC.SampleComplexity.Log2 z := by
  unfold OptimalPAC.SampleComplexity.Log2
  rw [Real.le_logb_iff_rpow_le (by norm_num) (by positivity)]
  simp

lemma l4_Log2_ge3 {z : ℝ} (hz : 8 ≤ z) : 3 ≤ OptimalPAC.SampleComplexity.Log2 z := by
  unfold OptimalPAC.SampleComplexity.Log2
  rw [Real.le_logb_iff_rpow_le (by norm_num) (by positivity)]
  norm_num
  exact hz

lemma l4_A_ge (d m : ℕ) (hd : 1 ≤ d) (δ : ℝ)
    (hA : 2 * ((d : ℝ) * OptimalPAC.SampleComplexity.Log2 (2 * Real.exp 1 * m / d) +
      OptimalPAC.SampleComplexity.Log2 (2 / δ)) < m) :
    4 ≤ (d : ℝ) * OptimalPAC.SampleComplexity.Log2 (2 * Real.exp 1 * m / d) +
      OptimalPAC.SampleComplexity.Log2 (2 / δ) := by
  have h1 := l4_Log2_ge (2 / δ)
  have h2 := l4_Log2_ge (2 * Real.exp 1 * m / d)
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  suffices h : 3 ≤ (d : ℝ) * OptimalPAC.SampleComplexity.Log2 (2 * Real.exp 1 * m / d) by linarith
  by_cases hd3 : 3 ≤ d
  · have : (3 : ℝ) ≤ d := by exact_mod_cast hd3
    nlinarith
  · have hd2 : (d : ℝ) ≤ 2 := by exact_mod_cast (by omega : d ≤ 2)
    have hm4 : (4 : ℝ) < m := by nlinarith
    have hm5 : (5 : ℝ) ≤ m := by
      have : 4 < m := by exact_mod_cast hm4
      exact_mod_cast (by omega : 5 ≤ m)
    have he : (2.7 : ℝ) < Real.exp 1 := by
      have := Real.exp_one_gt_d9; linarith
    have h8 : 8 ≤ 2 * Real.exp 1 * m / d := by
      rw [le_div_iff₀ (by linarith)]; nlinarith
    have := l4_Log2_ge3 h8
    nlinarith

lemma l4_numeric (d m : ℕ) (hd : 1 ≤ d) (hm : 1 ≤ m) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    2 * (ComputationalLearning.Phi d (2 * m) : ℝ) *
      (2 : ℝ) ^ (-((d : ℝ) * OptimalPAC.SampleComplexity.Log2 (2 * Real.exp 1 * m / d) +
        OptimalPAC.SampleComplexity.Log2 (2 / δ))) ≤ δ := by
  set a : ℝ := 2 * Real.exp 1 * m / d with ha
  set L : ℝ := OptimalPAC.SampleComplexity.Log2 a with hL
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hL1 : 1 ≤ L := l4_Log2_ge a
  -- the confidence term
  have h2δ : (2 : ℝ) < 2 / δ := by rw [lt_div_iff₀ hδ0]; linarith
  have hLδ : OptimalPAC.SampleComplexity.Log2 (2 / δ) = Real.logb 2 (2 / δ) := by
    unfold OptimalPAC.SampleComplexity.Log2; rw [max_eq_left h2δ.le]
  have hpowδ : (2 : ℝ) ^ (-OptimalPAC.SampleComplexity.Log2 (2 / δ)) = δ / 2 := by
    rw [hLδ, Real.rpow_neg (by norm_num), Real.rpow_logb (by norm_num) (by norm_num)
      (by positivity)]
    field_simp
  -- the growth term
  have hΦ : (ComputationalLearning.Phi d (2 * m) : ℝ) ≤ (2 : ℝ) ^ ((d : ℝ) * L) := by
    by_cases hdm : d ≤ 2 * m
    · have h1 := l4_phi_exp d (2 * m) hd hdm
      have ha2 : 2 ≤ a := by
        rw [ha, le_div_iff₀ hdpos]
        have : (d : ℝ) ≤ 2 * m := by exact_mod_cast hdm
        have := Real.add_one_le_exp 1
        nlinarith
      have hLa : L = Real.logb 2 a := by
        rw [hL]; unfold OptimalPAC.SampleComplexity.Log2; rw [max_eq_left ha2]
      have : (2 : ℝ) ^ ((d : ℝ) * L) = a ^ d := by
        rw [mul_comm, Real.rpow_mul (by norm_num), hLa,
          Real.rpow_logb (by norm_num) (by norm_num) (by linarith), Real.rpow_natCast]
      rw [this, ha]
      refine h1.trans (le_of_eq ?_)
      push_cast; ring_nf
    · push_neg at hdm
      calc (ComputationalLearning.Phi d (2 * m) : ℝ) ≤ 2 ^ (2 * m) := l4_phi_le_two_pow _ _
        _ ≤ 2 ^ d := pow_le_pow_right₀ (by norm_num) hdm.le
        _ = (2 : ℝ) ^ ((d : ℝ)) := (Real.rpow_natCast 2 d).symm
        _ ≤ (2 : ℝ) ^ ((d : ℝ) * L) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (le_mul_of_one_le_right hdpos.le hL1)
  have hsplit : (2 : ℝ) ^ (-((d : ℝ) * L + OptimalPAC.SampleComplexity.Log2 (2 / δ))) =
      (2 : ℝ) ^ (-((d : ℝ) * L)) * (δ / 2) := by
    rw [neg_add, Real.rpow_add (by norm_num), hpowδ]
  rw [hsplit]
  have hprod : (ComputationalLearning.Phi d (2 * m) : ℝ) * (2 : ℝ) ^ (-((d : ℝ) * L)) ≤ 1 := by
    rw [Real.rpow_neg (by norm_num), ← div_eq_mul_inv, div_le_one (by positivity)]
    exact hΦ
  have hp0 : (0 : ℝ) ≤ (2 : ℝ) ^ (-((d : ℝ) * L)) := by positivity
  nlinarith

open OptimalPAC.SampleComplexity MeasureTheory in
theorem solution {X : Type*} [MeasurableSpace X] (C : Set (X → Bool))
    (hCm : ∀ h ∈ C, Measurable h) (hC3 : 3 ≤ C.encard) (d : ℕ) (hd : vcDim C = d)
    (hWB : WellBehaved C)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (m : ℕ) (hm : 1 ≤ m) (f : X → Bool) (hf : f ∈ C)
    (P : Measure X) [IsProbabilityMeasure P] :
    Measure.pi (fun _ : Fin m => P)
      {z | ∃ h ∈ consistent C (labeled f z),
        2 / (m : ℝ) * ((d : ℝ) * Log2 (2 * Real.exp 1 * m / d) + Log2 (2 / δ)) < er P h f}
      ≤ ENNReal.ofReal δ := by
  have hfm : Measurable f := hCm f hf
  have hd1 : 1 ≤ d := l4_d_pos C hC3 d hd
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  set A : ℝ := (d : ℝ) * Log2 (2 * Real.exp 1 * m / d) + Log2 (2 / δ) with hAdef
  set t : ℝ := 2 / (m : ℝ) * A with htdef
  have htm2 : t * m / 2 = A := by rw [htdef]; field_simp
  by_cases ht1 : 1 ≤ t
  · have hempty : {z : Fin m → X | ∃ h ∈ consistent C (labeled f z), t < er P h f} = ∅ := by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_and,
        not_lt]
      intro h _
      have : er P h f ≤ 1 := by
        unfold er
        exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by rw [ENNReal.ofReal_one]; exact prob_le_one)
      linarith
    rw [hempty, measure_empty]; simp
  · push_neg at ht1
    have h2A : 2 * A < m := by
      have : t * m < 1 * m := mul_lt_mul_of_pos_right ht1 hmpos
      rw [show t * m = 2 * A by linarith [htm2]] at this; linarith
    have hA4 : 4 ≤ A := l4_A_ge d m hd1 δ h2A
    have ht0 : 0 < t := by rw [htdef]; positivity
    have htm : 8 / t ≤ m := by
      rw [div_le_iff₀ ht0]; linarith [htm2]
    obtain ⟨M, -, hAM, hμM⟩ := l4_core C hCm d (l4_vc_le C d hd) f hfm (l4_wb C hWB f hf) P ht0 m htm
    have hsub : {z : Fin m → X | ∃ h ∈ consistent C (labeled f z), t < er P h f} ⊆ M := by
      rintro z ⟨h, ⟨hC, hcons⟩, her⟩
      apply hAM
      refine ⟨h, hC, ?_, fun i hi => ?_⟩
      · unfold er at her
        have := ENNReal.ofReal_le_ofReal her.le
        rwa [ENNReal.ofReal_toReal (measure_ne_top _ _)] at this
      · have := hcons (z i, f (z i)) (by simp [labeled, List.mem_ofFn]; exact ⟨i, rfl, rfl⟩)
        exact hi this
    calc _ ≤ (Measure.pi fun _ : Fin m => P) M := measure_mono hsub
      _ ≤ _ := hμM
      _ ≤ ENNReal.ofReal δ := by
        apply ENNReal.ofReal_le_ofReal
        rw [htm2]
        exact l4_numeric d m hd1 hm δ hδ0 hδ1
