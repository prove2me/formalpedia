-- Prove2me | solution 1 for PrivateUniformGen.Characterization.theorem_1_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-20T04:03:17.728857+00:00
-- url     : https://prove2.me/submissions/4e41e177-2d1e-46e9-ba20-94a4ccfa258c

import Mathlib
import Definitions.Def_PrivateUniformGen_Characterization_Languages
import Definitions.Def_PrivateUniformGen_Characterization_Branching

set_option autoImplicit false

namespace PrivGenProof

open MeasureTheory Filter PrivateUniformGen.Characterization
open scoped ENNReal Classical

/-! ### Part 1: Measure, Probability, and Differential Privacy Primitives -/

section MeasurePrimitives

lemma measurableSet_subset {X : Type} [Countable X] (K : Set X) :
    MeasurableSet {Z : Set X | Z ⊆ K} := by
  have h : {Z : Set X | Z ⊆ K} = ⋂ x ∈ Kᶜ, {Z : Set X | x ∈ Z}ᶜ := by
    ext Z
    simp only [Set.mem_iInter, Set.mem_compl_iff]
    exact ⟨fun hsub x hx hxZ => hx (hsub hxZ),
      fun h x hxZ => by by_contra hxK; exact h x hxK hxZ⟩
  rw [h]
  exact MeasurableSet.biInter (Set.to_countable Kᶜ) fun x _ => (measurableSet_mem x).compl

lemma measurableSet_infinite {X : Type} [Countable X] :
    MeasurableSet {Z : Set X | Z.Infinite} := by
  by_cases hX : Finite X
  · have h : {Z : Set X | Z.Infinite} = ∅ := by
      ext Z
      simp [Set.toFinite Z]
    rw [h]
    exact MeasurableSet.empty
  · have : Infinite X := not_finite_iff_infinite.mp hX
    obtain ⟨e⟩ := nonempty_equiv_of_countable (α := ℕ) (β := X)
    have h : {Z : Set X | Z.Infinite} = ⋂ m : ℕ, ⋃ k ≥ m, {Z : Set X | e k ∈ Z} := by
      ext Z
      simp only [Set.mem_iInter, Set.mem_iUnion]
      constructor
      · intro hZ m
        have hpre : (e.symm '' Z).Infinite := hZ.image e.symm.injective.injOn
        obtain ⟨k, hkZ, hkm⟩ := hpre.exists_gt m
        obtain ⟨z, hzZ, rfl⟩ := hkZ
        exact ⟨e.symm z, hkm.le, by simpa using hzZ⟩
      · intro h hZfin
        have hpre : (e.symm '' Z).Finite := hZfin.image _
        obtain ⟨B, hB⟩ := hpre.bddAbove
        obtain ⟨k, hkB, hkZ⟩ := h (B + 1)
        have : k ≤ B := hB ⟨e k, hkZ, e.symm_apply_apply k⟩
        omega
    rw [h]
    exact MeasurableSet.iInter fun m =>
      MeasurableSet.biUnion (Set.to_countable _) fun k _ => measurableSet_mem (e k)

lemma infinite_X_of_languageClass {X : Type} (C : LanguageClass X) : Infinite X := by
  obtain ⟨L, hL⟩ := C.nonempty
  have : Infinite L := (C.infinite L hL).to_subtype
  exact Infinite.of_injective (Subtype.val : L → X) Subtype.val_injective

lemma near_of_eq_except {X : Type*} {n : ℕ} {S S' : Fin n → X} (i₀ : Fin n)
    (h : ∀ j, j ≠ i₀ → S j = S' j) : Near S S' := by
  by_cases h_eq : S i₀ = S' i₀
  · left
    ext j
    by_cases hj : j = i₀
    · subst hj; exact h_eq
    · exact h j hj
  · right
    exact ⟨i₀, h_eq, h⟩

lemma near_symm {X : Type*} {n : ℕ} {S S' : Fin n → X} (h : Near S S') : Near S' S := by
  rcases h with rfl | ⟨i, hne, hrest⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨i, hne.symm, fun j hj => (hrest j hj).symm⟩

lemma isDP_near_le {X Y : Type*} [MeasurableSpace Y] {n : ℕ}
    {A : Mechanism X Y n} {ε δ : ℝ} (hdp : IsDP A ε δ) (hε : 0 ≤ ε) (hδ : 0 ≤ δ)
    {S S' : Fin n → X} (hnear : Near S S') {O : Set Y} (hO : MeasurableSet O) :
    (A S : Measure Y).real O ≤ Real.exp ε * (A S' : Measure Y).real O + δ := by
  rcases hnear with rfl | hnb
  · have h1 : 1 ≤ Real.exp ε := Real.one_le_exp hε
    have hnonneg : 0 ≤ (A S : Measure Y).real O := measureReal_nonneg
    nlinarith
  · exact hdp S S' hnb O hO

/-- Finite-support `ProbabilityMeasure` from nonnegative weights summing to `1`. -/
noncomputable def finitePM {Y ι : Type*} [MeasurableSpace Y] [Fintype ι]
    (w : ι → ℝ) (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (f : ι → Y) :
    ProbabilityMeasure Y :=
  ⟨∑ i : ι, ENNReal.ofReal (w i) • Measure.dirac (f i),
    ⟨by
      simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
        Measure.dirac_apply' _ MeasurableSet.univ, Set.indicator_univ, Pi.one_apply,
        smul_eq_mul, mul_one]
      rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hw0 i), hw1, ENNReal.ofReal_one]⟩⟩

lemma finitePM_real_apply {Y ι : Type*} [MeasurableSpace Y] [Fintype ι]
    (w : ι → ℝ) (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (f : ι → Y)
    {O : Set Y} (hO : MeasurableSet O) :
    (finitePM w hw0 hw1 f : Measure Y).real O =
      ∑ i : ι, if f i ∈ O then w i else 0 := by
  have hval : (finitePM w hw0 hw1 f : Measure Y) O =
      ∑ i : ι, ENNReal.ofReal (if f i ∈ O then w i else 0) := by
    change (∑ i : ι, ENNReal.ofReal (w i) • Measure.dirac (f i)) O = _
    simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
      Measure.dirac_apply' _ hO, Set.indicator_apply, Pi.one_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp
  simp only [Measure.real, hval]
  rw [ENNReal.toReal_sum (fun i _ => ENNReal.ofReal_ne_top)]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with hi
  · exact ENNReal.toReal_ofReal (hw0 i)
  · simp

lemma finitePM_ae {Y ι : Type*} [MeasurableSpace Y] [Fintype ι]
    (w : ι → ℝ) (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (f : ι → Y)
    {P : Y → Prop} (hmeas : MeasurableSet {y | P y})
    (hP : ∀ i, w i ≠ 0 → P (f i)) :
    ∀ᵐ y ∂(finitePM w hw0 hw1 f : Measure Y), P y := by
  rw [ae_iff]
  change (∑ i : ι, ENNReal.ofReal (w i) • Measure.dirac (f i)) {y | ¬ P y} = 0
  have hcompl : MeasurableSet {y | ¬ P y} := hmeas.compl
  simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
    Measure.dirac_apply' _ hcompl, Set.indicator_apply, Pi.one_apply, smul_eq_mul]
  refine Finset.sum_eq_zero fun i _ => ?_
  by_cases hw : w i = 0
  · simp [hw]
  · have hi : f i ∉ {y | ¬ P y} := fun h => h (hP i hw)
    simp [hi]

/-- Uniform average of pushforwards of `ProbabilityMeasure`s over a nonempty `Fintype`. -/
noncomputable def avgMapPM {Y Z Θ : Type*} [MeasurableSpace Y] [MeasurableSpace Z]
    [Fintype Θ] [Nonempty Θ]
    (μ : Θ → ProbabilityMeasure Y) (g : Θ → Y → Z) (hg : ∀ θ, Measurable (g θ)) :
    ProbabilityMeasure Z :=
  ⟨((Fintype.card Θ : ℝ≥0∞)⁻¹) • ∑ θ : Θ, (μ θ : Measure Y).map (g θ),
    ⟨by
      have hcard_pos : 0 < Fintype.card Θ := Fintype.card_pos
      have hcard_ne_zero : (Fintype.card Θ : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr hcard_pos.ne'
      have hcard_ne_top : (Fintype.card Θ : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
      simp only [Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply, smul_eq_mul]
      have hsum : (∑ θ : Θ, ((μ θ : Measure Y).map (g θ)) Set.univ) = Fintype.card Θ := by
        have h1 : ∀ θ : Θ, ((μ θ : Measure Y).map (g θ)) Set.univ = 1 := fun θ => by
          rw [Measure.map_apply (hg θ) MeasurableSet.univ, Set.preimage_univ, measure_univ]
        simp [h1]
      rw [hsum, ENNReal.inv_mul_cancel hcard_ne_zero hcard_ne_top]⟩⟩

lemma avgMapPM_real_apply {Y Z Θ : Type*} [MeasurableSpace Y] [MeasurableSpace Z]
    [Fintype Θ] [Nonempty Θ]
    (μ : Θ → ProbabilityMeasure Y) (g : Θ → Y → Z) (hg : ∀ θ, Measurable (g θ))
    {O : Set Z} (hO : MeasurableSet O) :
    (avgMapPM μ g hg : Measure Z).real O =
      ((Fintype.card Θ : ℝ)⁻¹) * ∑ θ : Θ, (μ θ : Measure Y).real (g θ ⁻¹' O) := by
  have hval : (avgMapPM μ g hg : Measure Z) O =
      ((Fintype.card Θ : ℝ≥0∞)⁻¹) * ∑ θ : Θ, (μ θ : Measure Y) (g θ ⁻¹' O) := by
    change (((Fintype.card Θ : ℝ≥0∞)⁻¹) • ∑ θ : Θ, (μ θ : Measure Y).map (g θ)) O = _
    simp only [Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply, smul_eq_mul]
    congr 1
    refine Finset.sum_congr rfl fun θ _ => ?_
    exact Measure.map_apply (hg θ) hO
  simp only [Measure.real, hval, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  congr 1
  exact ENNReal.toReal_sum fun θ _ => measure_ne_top (μ θ : Measure Y) _

lemma isDP_avgMap {α X Y Z Θ : Type*} [MeasurableSpace Y] [MeasurableSpace Z]
    [Fintype Θ] [Nonempty Θ] {m n : ℕ}
    (A : Mechanism X Y n) {ε δ : ℝ} (hdp : IsDP A ε δ) (hε : 0 ≤ ε) (hδ : 0 ≤ δ)
    (enc : Θ → (Fin m → α) → (Fin n → X))
    (henc : ∀ θ {x x' : Fin m → α}, Neighbors x x' → Near (enc θ x) (enc θ x'))
    (g : Θ → Y → Z) (hg : ∀ θ, Measurable (g θ)) :
    IsDP (fun x => avgMapPM (fun θ => A (enc θ x)) g hg) ε δ := by
  intro x x' hnb O hO
  rw [avgMapPM_real_apply _ _ _ hO, avgMapPM_real_apply _ _ _ hO]
  have hcard_pos : (0 : ℝ) < Fintype.card Θ := Nat.cast_pos.mpr Fintype.card_pos
  have hterm : ∀ θ : Θ,
      (A (enc θ x) : Measure Y).real (g θ ⁻¹' O) ≤
        Real.exp ε * (A (enc θ x') : Measure Y).real (g θ ⁻¹' O) + δ := fun θ =>
    isDP_near_le hdp hε hδ (henc θ hnb) (hg θ hO)
  have hsum : ∑ θ : Θ, (A (enc θ x) : Measure Y).real (g θ ⁻¹' O) ≤
      Real.exp ε * (∑ θ : Θ, (A (enc θ x') : Measure Y).real (g θ ⁻¹' O)) +
        (Fintype.card Θ : ℝ) * δ := by
    calc ∑ θ : Θ, (A (enc θ x) : Measure Y).real (g θ ⁻¹' O)
        ≤ ∑ θ : Θ, (Real.exp ε * (A (enc θ x') : Measure Y).real (g θ ⁻¹' O) + δ) :=
          Finset.sum_le_sum fun θ _ => hterm θ
      _ = Real.exp ε * (∑ θ : Θ, (A (enc θ x') : Measure Y).real (g θ ⁻¹' O)) +
            (Fintype.card Θ : ℝ) * δ := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
            nsmul_eq_mul]
  have hinv_nonneg : 0 ≤ ((Fintype.card Θ : ℝ)⁻¹) := inv_nonneg.mpr hcard_pos.le
  calc ((Fintype.card Θ : ℝ)⁻¹) * ∑ θ : Θ, (A (enc θ x) : Measure Y).real (g θ ⁻¹' O)
      ≤ ((Fintype.card Θ : ℝ)⁻¹) *
          (Real.exp ε * (∑ θ : Θ, (A (enc θ x') : Measure Y).real (g θ ⁻¹' O)) +
            (Fintype.card Θ : ℝ) * δ) :=
        mul_le_mul_of_nonneg_left hsum hinv_nonneg
    _ = Real.exp ε * (((Fintype.card Θ : ℝ)⁻¹) *
          ∑ θ : Θ, (A (enc θ x') : Measure Y).real (g θ ⁻¹' O)) + δ := by
        have hne : (Fintype.card Θ : ℝ) ≠ 0 := hcard_pos.ne'
        field_simp [hne]

lemma sum_disjoint_real_le_one {Y ι : Type*} [MeasurableSpace Y] [Fintype ι]
    (μ : ProbabilityMeasure Y) (E : ι → Set Y)
    (hmeas : ∀ i, MeasurableSet (E i))
    (hdisj : Pairwise fun i j => Disjoint (E i) (E j)) :
    ∑ i : ι, (μ : Measure Y).real (E i) ≤ 1 := by
  have hunion : (∑ i : ι, (μ : Measure Y) (E i)) = (μ : Measure Y) (⋃ i : ι, E i) := by
    rw [measure_iUnion hdisj hmeas, tsum_fintype]
  have hle : (∑ i : ι, (μ : Measure Y) (E i)) ≤ 1 := by
    rw [hunion]
    exact prob_le_one
  have hto := ENNReal.toReal_mono ENNReal.one_ne_top hle
  rw [ENNReal.toReal_one, ENNReal.toReal_sum (fun i _ => measure_ne_top (μ : Measure Y) _)] at hto
  exact hto

end MeasurePrimitives

/-! ### Part 2: Combinatorial Foundations (Closures, Ranks, Helly, Cores, Profiles) -/

section Combinatorics

lemma closureDim_lt_top_iff {X : Type*} (C : LanguageClass X) :
    closureDim C < ⊤ ↔ closureSizeSup C < ⊤ := by
  unfold closureDim
  split_ifs with h0 hfin htop
  · simp [h0]
  · simp [h0]
    exact WithTop.coe_lt_top (-1 : ℤ)
  · simp [htop]
  · simp [lt_top_iff_ne_top, htop]

lemma closure_mono {X : Type*} (C : LanguageClass X) {T₁ T₂ : Set X} (h : T₁ ⊆ T₂) :
    closure C T₁ ⊆ closure C T₂ :=
  Set.sInter_subset_sInter fun _ hL => ⟨hL.1, h.trans hL.2⟩

lemma subset_closure {X : Type*} (C : LanguageClass X) (T : Set X) :
    T ⊆ closure C T :=
  Set.subset_sInter fun _ hL => hL.2

lemma closure_subset_of_mem {X : Type*} (C : LanguageClass X) {T L : Set X}
    (hL : L ∈ C.languages) (hTL : T ⊆ L) :
    closure C T ⊆ L :=
  Set.sInter_subset_of_mem ⟨hL, hTL⟩

lemma mem_infiniteClosure_of_mem {X : Type*} (C : LanguageClass X) {L : Set X}
    (hL : L ∈ C.languages) : L ∈ infiniteClosure C :=
  ⟨C.infinite L hL, ⟨{L}, Set.singleton_nonempty L, Set.singleton_subset_iff.mpr hL,
    (Set.sInter_singleton L).symm⟩⟩

lemma closure_subset_of_mem_infiniteClosure {X : Type*} (C : LanguageClass X)
    {T K : Set X} (hK : K ∈ infiniteClosure C) (hTK : T ⊆ K) :
    closure C T ⊆ K := by
  obtain ⟨_, F, _, hFC, rfl⟩ := hK
  refine Set.subset_sInter fun L hLF => ?_
  exact closure_subset_of_mem C (hFC hLF) (hTK.trans (Set.sInter_subset_of_mem hLF))

lemma sInter_mem_infiniteClosure {X : Type*} (C : LanguageClass X) {F : Set (Set X)}
    (hne : F.Nonempty) (hF : F ⊆ infiniteClosure C) (hinf : (⋂₀ F).Infinite) :
    ⋂₀ F ∈ infiniteClosure C := by
  refine ⟨hinf, ⟨{L ∈ C.languages | ∃ K ∈ F, K ⊆ L}, ?_, ?_, ?_⟩⟩
  · obtain ⟨K₀, hK₀⟩ := hne
    obtain ⟨_, F₀, ⟨L₀, hL₀⟩, hF₀C, hK₀eq⟩ := hF hK₀
    exact ⟨L₀, hF₀C hL₀, K₀, hK₀, hK₀eq ▸ Set.sInter_subset_of_mem hL₀⟩
  · intro L hL
    exact hL.1
  · ext x
    simp only [Set.mem_sInter]
    constructor
    · intro hx L ⟨_, K, hKF, hKL⟩
      exact hKL (hx K hKF)
    · intro hx K hKF
      obtain ⟨_, F_K, _, hF_KC, rfl⟩ := hF hKF
      intro L hLF_K
      exact hx L ⟨hF_KC hLF_K, _, hKF, Set.sInter_subset_of_mem hLF_K⟩

lemma inter_mem_infiniteClosure {X : Type*} (C : LanguageClass X) {A B : Set X}
    (hA : A ∈ infiniteClosure C) (hB : B ∈ infiniteClosure C) (hinf : (A ∩ B).Infinite) :
    A ∩ B ∈ infiniteClosure C := by
  have h := sInter_mem_infiniteClosure C (F := {A, B}) ⟨A, by simp⟩
    (by
      intro K hK
      rcases Set.mem_insert_iff.mp hK with rfl | hKB
      · exact hA
      · rw [Set.mem_singleton_iff.mp hKB]; exact hB)
    (by simpa [Set.sInter_insert, Set.sInter_singleton] using hinf)
  simpa [Set.sInter_insert, Set.sInter_singleton] using h

lemma hasTree_mem_infiniteClosure {X : Type*} {C : LanguageClass X} {ar : ℕ∞} {d : ℕ} {K : Set X}
    (h : HasTree C ar d K) : K ∈ infiniteClosure C := by
  cases h with
  | leaf _ hK => exact hK
  | branch _ hK _ _ _ _ _ _ => exact hK

lemma hasTree_pos {X : Type*} {C : LanguageClass X} {ar : ℕ∞} {d : ℕ} {K : Set X}
    (h : HasTree C ar d K) : 1 ≤ d := by
  cases h with
  | leaf _ _ => exact le_refl 1
  | branch hd _ _ _ _ _ _ _ => omega

lemma hasTree_mono_root {X : Type*} {C : LanguageClass X} {ar : ℕ∞} {d : ℕ} {H K : Set X}
    (h : HasTree C ar d H) (hK : K ∈ infiniteClosure C) (hHK : H ⊆ K) :
    HasTree C ar d K := by
  cases h with
  | leaf _ _ => exact HasTree.leaf K hK
  | branch hd _ F hne hcard hsub htree hfin =>
      exact HasTree.branch hd hK F hne hcard (fun T hT => (hsub T hT).trans hHK) htree hfin

lemma hasTree_le {X : Type*} {C : LanguageClass X} {ar : ℕ∞} {d : ℕ} {K : Set X}
    (h : HasTree C ar d K) : ∀ {m : ℕ}, 1 ≤ m → m ≤ d → HasTree C ar m K := by
  induction h with
  | leaf K hK =>
      intro m hm1 hmd
      have : m = 1 := by omega
      subst this
      exact HasTree.leaf K hK
  | @branch d' K hd' hK F hne hcard hsub htree hfin ih =>
      intro m hm1 hmd
      rcases eq_or_lt_of_le hmd with rfl | hlt
      · exact HasTree.branch hd' hK F hne hcard hsub htree hfin
      · obtain ⟨T, hTF⟩ := hne
        exact hasTree_mono_root (ih T hTF hm1 (by omega)) hK (hsub T hTF)

/-- Natural-valued rank when `nbDim C ⊤ < ⊤`. -/
noncomputable def rk {X : Type*} (C : LanguageClass X) (K : Set X) : ℕ :=
  (rank C ⊤ K).toNat

lemma le_rank_of_hasTree {X : Type*} {C : LanguageClass X} {ar : ℕ∞} {d : ℕ} {K : Set X}
    (h : HasTree C ar d K) : (d : ℕ∞) ≤ rank C ar K :=
  le_iSup₂ (f := fun (d : ℕ) (_ : HasTree C ar d K) => (d : ℕ∞)) d h

lemma rank_le_nbDim {X : Type*} {C : LanguageClass X} {ar : ℕ∞} {K : Set X}
    (hK : K ∈ infiniteClosure C) : rank C ar K ≤ nbDim C ar :=
  le_iSup₂ (f := fun (K : Set X) (_ : K ∈ infiniteClosure C) => rank C ar K) K hK

lemma rk_coe {X : Type*} {C : LanguageClass X} (hnb : nbDim C ⊤ < ⊤) {K : Set X}
    (hK : K ∈ infiniteClosure C) : ((rk C K : ℕ) : ℕ∞) = rank C ⊤ K := by
  have hlt : rank C ⊤ K < ⊤ := (rank_le_nbDim hK).trans_lt hnb
  exact ENat.natCast_toNat hlt.ne

lemma rk_pos {X : Type*} {C : LanguageClass X} (hnb : nbDim C ⊤ < ⊤) {K : Set X}
    (hK : K ∈ infiniteClosure C) : 1 ≤ rk C K := by
  have h1 : (1 : ℕ∞) ≤ rank C ⊤ K := le_rank_of_hasTree (HasTree.leaf K hK)
  rw [← rk_coe hnb hK] at h1
  exact Nat.cast_le.mp h1

lemma rk_le_nbDim {X : Type*} {C : LanguageClass X} (hnb : nbDim C ⊤ < ⊤) {K : Set X}
    (hK : K ∈ infiniteClosure C) : rk C K ≤ (nbDim C ⊤).toNat := by
  have hle : rank C ⊤ K ≤ nbDim C ⊤ := rank_le_nbDim hK
  rw [← rk_coe hnb hK, ← ENat.natCast_toNat hnb.ne] at hle
  exact Nat.cast_le.mp hle

lemma hasTree_le_rk {X : Type*} {C : LanguageClass X} (hnb : nbDim C ⊤ < ⊤) {K : Set X}
    (hK : K ∈ infiniteClosure C) {k : ℕ} (ht : HasTree C ⊤ k K) : k ≤ rk C K := by
  have hle : (k : ℕ∞) ≤ rank C ⊤ K := le_rank_of_hasTree ht
  rw [← rk_coe hnb hK] at hle
  exact Nat.cast_le.mp hle

lemma hasTree_rk {X : Type*} {C : LanguageClass X} (hnb : nbDim C ⊤ < ⊤) {K : Set X}
    (hK : K ∈ infiniteClosure C) : HasTree C ⊤ (rk C K) K := by
  by_contra hnot
  have hpos : 1 ≤ rk C K := rk_pos hnb hK
  have hub : rank C ⊤ K ≤ ((rk C K - 1 : ℕ) : ℕ∞) := by
    refine iSup₂_le fun k hk => ?_
    have hkle : k ≤ rk C K := hasTree_le_rk hnb hK hk
    have hkne : k ≠ rk C K := fun heq => hnot (heq ▸ hk)
    exact Nat.cast_le.mpr (by omega)
  rw [← rk_coe hnb hK] at hub
  have : rk C K ≤ rk C K - 1 := Nat.cast_le.mp hub
  omega

lemma rk_mono {X : Type*} {C : LanguageClass X} (hnb : nbDim C ⊤ < ⊤) {H K : Set X}
    (hH : H ∈ infiniteClosure C) (hK : K ∈ infiniteClosure C) (hHK : H ⊆ K) :
    rk C H ≤ rk C K :=
  hasTree_le_rk hnb hK (hasTree_mono_root (hasTree_rk hnb hH) hK hHK)

/-- Lemma 4.7: Finite-intersection Helly bound `d + 1` on `infiniteClosure C`. -/
lemma helly_infiniteClosure {X : Type*} {C : LanguageClass X} (hnb : nbDim C ⊤ < ⊤)
    {F : Set (Set X)} (hne : F.Nonempty) (hF : F ⊆ infiniteClosure C) (hfin : (⋂₀ F).Finite) :
    ∃ G : Finset (Set X), G.Nonempty ∧ (↑G : Set (Set X)) ⊆ F ∧
      G.card ≤ (nbDim C ⊤).toNat + 1 ∧ (⋂₀ (↑G : Set (Set X))).Finite := by
  by_contra hno
  have hno' : ∀ G : Finset (Set X), G.Nonempty → (↑G : Set (Set X)) ⊆ F →
      G.card ≤ (nbDim C ⊤).toNat + 1 → (⋂₀ (↑G : Set (Set X))).Infinite := by
    intro G hGne hGF hGcard
    by_contra hnotinf
    exact hno ⟨G, hGne, hGF, hGcard, Set.not_infinite.mp hnotinf⟩
  set d := (nbDim C ⊤).toNat
  have htree_step : ∀ r : ℕ, r ≤ d → ∀ G : Finset (Set X),
      G.Nonempty → (↑G : Set (Set X)) ⊆ F → G.card ≤ d + 1 - r →
      HasTree C ⊤ (r + 1) (⋂₀ (↑G : Set (Set X))) := by
    intro r
    induction r with
    | zero =>
        intro _ G hGne hGF hGcard
        have hinf : (⋂₀ (↑G : Set (Set X))).Infinite := hno' G hGne hGF (by omega)
        exact HasTree.leaf _ (sInter_mem_infiniteClosure C
          (Finset.coe_nonempty.mpr hGne) (hGF.trans hF) hinf)
    | succ r ih =>
        intro hrd G hGne hGF hGcard
        have hK_inf : (⋂₀ (↑G : Set (Set X))).Infinite := hno' G hGne hGF (by omega)
        have hK_ic : ⋂₀ (↑G : Set (Set X)) ∈ infiniteClosure C :=
          sInter_mem_infiniteClosure C (Finset.coe_nonempty.mpr hGne) (hGF.trans hF) hK_inf
        let Ch : Set (Set X) := (fun A => ⋂₀ (↑G : Set (Set X)) ∩ A) '' F
        obtain ⟨A₀, hA₀⟩ := hne
        refine HasTree.branch (by omega) hK_ic Ch ⟨_, ⟨A₀, hA₀, rfl⟩⟩ le_top ?_ ?_ ?_
        · rintro _ ⟨A, _, rfl⟩
          exact Set.inter_subset_left
        · rintro _ ⟨A, hAF, rfl⟩
          have hG'ne : (insert A G).Nonempty := Finset.insert_nonempty A G
          have hG'F : (↑(insert A G) : Set (Set X)) ⊆ F := by
            rw [Finset.coe_insert]
            exact Set.insert_subset hAF hGF
          have hG'card : (insert A G).card ≤ d + 1 - r := by
            have hle := Finset.card_insert_le A G
            omega
          have hsInter : ⋂₀ (↑(insert A G) : Set (Set X)) = ⋂₀ (↑G : Set (Set X)) ∩ A := by
            rw [Finset.coe_insert, Set.sInter_insert, Set.inter_comm]
          dsimp only
          rw [← hsInter]
          exact ih (by omega) (insert A G) hG'ne hG'F hG'card
        · refine hfin.subset fun x hx A hAF => ?_
          exact (hx _ ⟨A, hAF, rfl⟩).2
  obtain ⟨F₁, hF₁⟩ := hne
  have ht := htree_step d (le_refl d) {F₁} (Finset.singleton_nonempty F₁)
    (by simp [hF₁]) (by simp)
  rw [Finset.coe_singleton, Set.sInter_singleton] at ht
  have hle : d + 1 ≤ rk C F₁ := hasTree_le_rk hnb (hF hF₁) ht
  have hub : rk C F₁ ≤ d := rk_le_nbDim hnb (hF hF₁)
  omega

/-- Definition 5.1: Rank core of `K`. -/
noncomputable def core {X : Type*} (C : LanguageClass X) (K : Set X) : Set X :=
  ⋂₀ {T ∈ infiniteClosure C | T ⊆ K ∧ rk C T = rk C K}

lemma core_subset {X : Type*} {C : LanguageClass X} {K : Set X} (hK : K ∈ infiniteClosure C) :
    core C K ⊆ K :=
  Set.sInter_subset_of_mem ⟨hK, Set.Subset.rfl, rfl⟩

/-- Lemma 5.2: `core C K ∈ infiniteClosure C`. -/
lemma core_mem_infiniteClosure {X : Type*} {C : LanguageClass X} (hnb : nbDim C ⊤ < ⊤)
    {K : Set X} (hK : K ∈ infiniteClosure C) :
    core C K ∈ infiniteClosure C := by
  let Fam : Set (Set X) := {T ∈ infiniteClosure C | T ⊆ K ∧ rk C T = rk C K}
  have hKFam : K ∈ Fam := ⟨hK, Set.Subset.rfl, rfl⟩
  have hFam_sub : Fam ⊆ infiniteClosure C := fun _ h => h.1
  have hinf : (⋂₀ Fam).Infinite := by
    by_contra hnot
    have hfin : (⋂₀ Fam).Finite := Set.not_infinite.mp hnot
    have hbranch : HasTree C ⊤ (rk C K + 1) K :=
      HasTree.branch (rk_pos hnb hK) hK Fam ⟨K, hKFam⟩ le_top (fun _ h => h.2.1)
        (fun T h => h.2.2 ▸ hasTree_rk hnb h.1) hfin
    have := hasTree_le_rk hnb hK hbranch
    omega
  exact sInter_mem_infiniteClosure C ⟨K, hKFam⟩ hFam_sub hinf

/-- Lemma 5.3: Core anti-monotonicity on equal-rank nested sets, and stationarity. -/
lemma core_anti_of_rk_eq {X : Type*} {C : LanguageClass X} {H K : Set X}
    (hHK : H ⊆ K) (hrk : rk C H = rk C K) :
    core C K ⊆ core C H :=
  Set.sInter_subset_sInter fun _ hT => ⟨hT.1, hT.2.1.trans hHK, hT.2.2.trans hrk⟩

lemma core_eq_of_rk_core_eq {X : Type*} {C : LanguageClass X} (hnb : nbDim C ⊤ < ⊤)
    {H K : Set X} (hH : H ∈ infiniteClosure C) (hK : K ∈ infiniteClosure C)
    (hHK : H ⊆ K) (hrk : rk C H = rk C K) (hc : rk C (core C K) = rk C K) :
    core C H = core C K := by
  refine Set.Subset.antisymm ?_ (core_anti_of_rk_eq hHK hrk)
  have hc_ic : core C K ∈ infiniteClosure C := core_mem_infiniteClosure hnb hK
  have hc_sub_H : core C K ⊆ H :=
    Set.sInter_subset_of_mem ⟨hH, hHK, hrk⟩
  exact Set.sInter_subset_of_mem ⟨hc_ic, hc_sub_H, hc.trans hrk.symm⟩

/-- Definitions 5.4 & 5.5: Profile and iterated core. -/
noncomputable def profile {X : Type*} (C : LanguageClass X) (K : Set X) : List ℕ :=
  if h : rk C (core C K) < rk C K then
    rk C K :: profile C (core C K)
  else
    [rk C K]
termination_by rk C K
decreasing_by exact h

noncomputable def iterCore {X : Type*} (C : LanguageClass X) (K : Set X) : Set X :=
  if h : rk C (core C K) < rk C K then
    iterCore C (core C K)
  else
    core C K
termination_by rk C K
decreasing_by exact h

lemma iterCore_mem_infiniteClosure {X : Type*} {C : LanguageClass X} (hnb : nbDim C ⊤ < ⊤) :
    ∀ K : Set X, K ∈ infiniteClosure C → iterCore C K ∈ infiniteClosure C ∧ iterCore C K ⊆ K := by
  have aux : ∀ m : ℕ, ∀ K : Set X, rk C K = m → K ∈ infiniteClosure C →
      iterCore C K ∈ infiniteClosure C ∧ iterCore C K ⊆ K := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
        intro K h_rk hK
        rw [iterCore]
        split_ifs with hlt
        · have hc_ic := core_mem_infiniteClosure hnb hK
          obtain ⟨h1, h2⟩ := ih (rk C (core C K)) (h_rk ▸ hlt) (core C K) rfl hc_ic
          exact ⟨h1, h2.trans (core_subset hK)⟩
        · exact ⟨core_mem_infiniteClosure hnb hK, core_subset hK⟩
  exact fun K hK => aux (rk C K) K rfl hK

/-- Strict-decreasing valid profile lists in `{1, ..., D}`, expressed via `List.Pairwise (· > ·)`. -/
def IsValidProfile (D : ℕ) (σ : List ℕ) : Prop :=
  σ.Pairwise (· > ·) ∧ ∀ x ∈ σ, 1 ≤ x ∧ x ≤ D

lemma profile_valid {X : Type*} {C : LanguageClass X} (hnb : nbDim C ⊤ < ⊤) :
    ∀ K : Set X, K ∈ infiniteClosure C →
      profile C K ≠ [] ∧ IsValidProfile (nbDim C ⊤).toNat (profile C K) ∧
      (profile C K).head? = some (rk C K) := by
  have aux : ∀ m : ℕ, ∀ K : Set X, rk C K = m → K ∈ infiniteClosure C →
      profile C K ≠ [] ∧ IsValidProfile (nbDim C ⊤).toNat (profile C K) ∧
      (profile C K).head? = some (rk C K) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
        intro K h_rk hK
        rw [profile]
        split_ifs with hlt
        · have hc_ic := core_mem_infiniteClosure hnb hK
          obtain ⟨hne, ⟨hpw, hmem⟩, hhead⟩ :=
            ih (rk C (core C K)) (h_rk ▸ hlt) (core C K) rfl hc_ic
          refine ⟨List.cons_ne_nil _ _, ⟨?_, ?_⟩, rfl⟩
          · refine List.pairwise_cons.mpr ⟨fun z hz => ?_, hpw⟩
            cases htl : profile C (core C K) with
            | nil => exact absurd htl hne
            | cons y ys =>
                rw [htl] at hz hpw hhead
                simp only [List.head?_cons, Option.some.injEq] at hhead
                rcases List.mem_cons.mp hz with hzy_eq | hzys
                · omega
                · have hzy : y > z := (List.pairwise_cons.mp hpw).1 z hzys
                  omega
          · intro x hx
            rcases List.mem_cons.mp hx with rfl | hxtl
            · exact ⟨rk_pos hnb hK, rk_le_nbDim hnb hK⟩
            · exact hmem x hxtl
        · refine ⟨List.cons_ne_nil _ _, ⟨List.pairwise_singleton _ _, ?_⟩, rfl⟩
          intro x hx
          rw [List.mem_singleton.mp hx]
          exact ⟨rk_pos hnb hK, rk_le_nbDim hnb hK⟩
  exact fun K hK => aux (rk C K) K rfl hK

/-- Lemma 5.8: Nested sets in `infiniteClosure C` with equal profiles have equal `iterCore`. -/
lemma iterCore_eq_of_profile_eq {X : Type*} {C : LanguageClass X} (hnb : nbDim C ⊤ < ⊤) :
    ∀ H K : Set X, H ∈ infiniteClosure C → K ∈ infiniteClosure C →
      H ⊆ K → profile C H = profile C K → iterCore C H = iterCore C K := by
  have aux : ∀ m : ℕ, ∀ H K : Set X, rk C K = m →
      H ∈ infiniteClosure C → K ∈ infiniteClosure C →
      H ⊆ K → profile C H = profile C K → iterCore C H = iterCore C K := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
        intro H K h_rk hH hK hHK hprof
        have hrk_eq : rk C H = rk C K := by
          have h1 := (profile_valid hnb H hH).2.2
          have h2 := (profile_valid hnb K hK).2.2
          rw [hprof, h2] at h1
          exact Option.some.inj h1.symm
        have hcH_le : rk C (core C H) ≤ rk C H :=
          rk_mono hnb (core_mem_infiniteClosure hnb hH) hH (core_subset hH)
        have hcK_le : rk C (core C K) ≤ rk C K :=
          rk_mono hnb (core_mem_infiniteClosure hnb hK) hK (core_subset hK)
        rw [profile] at hprof
        nth_rw 2 [profile] at hprof
        by_cases hltH : rk C (core C H) < rk C H <;> by_cases hltK : rk C (core C K) < rk C K
        · simp only [hltH, hltK, ↓reduceDIte] at hprof
          injection hprof with _ htl
          have h1 : iterCore C H = iterCore C (core C H) := by rw [iterCore, dif_pos hltH]
          have h2 : iterCore C K = iterCore C (core C K) := by rw [iterCore, dif_pos hltK]
          rw [h1, h2]
          exact (ih (rk C (core C H)) (by omega) (core C K) (core C H) rfl
            (core_mem_infiniteClosure hnb hK) (core_mem_infiniteClosure hnb hH)
            (core_anti_of_rk_eq hHK hrk_eq) htl.symm).symm
        · simp only [hltH, hltK, ↓reduceDIte] at hprof
          injection hprof with _ htl
          exact absurd htl (profile_valid hnb (core C H) (core_mem_infiniteClosure hnb hH)).1
        · simp only [hltH, hltK, ↓reduceDIte] at hprof
          injection hprof with _ htl
          exact absurd htl.symm (profile_valid hnb (core C K) (core_mem_infiniteClosure hnb hK)).1
        · have hcK_eq : rk C (core C K) = rk C K := by omega
          have h1 : iterCore C H = core C H := by rw [iterCore, dif_neg hltH]
          have h2 : iterCore C K = core C K := by rw [iterCore, dif_neg hltK]
          rw [h1, h2]
          exact core_eq_of_rk_core_eq hnb hH hK hHK hrk_eq hcK_eq
  exact fun H K hH hK hHK hp => aux (rk C K) H K rfl hH hK hHK hp

/-- Explicit integer encoding `pCode D σ < 2 ^ D` representing the paper's order `⪯_D`. -/
def pCode : ℕ → List ℕ → ℕ
  | 0, _ => 0
  | d + 1, [] => 2 ^ (d + 1) - 1
  | d + 1, x :: τ =>
      if x = d + 1 then
        if τ = [] then 2 ^ d - 1 else (2 ^ d - 2) - pCode d τ
      else
        2 ^ d + pCode d (x :: τ)

lemma validProfile_tail_of_eq {d : ℕ} {τ : List ℕ}
    (hv : IsValidProfile (d + 1) ((d + 1) :: τ)) : IsValidProfile d τ := by
  rcases hv with ⟨hpw, hmem⟩
  obtain ⟨hlt, hpw_tl⟩ := List.pairwise_cons.mp hpw
  refine ⟨hpw_tl, fun y hy => ?_⟩
  have hy1 := hmem y (List.mem_cons_of_mem _ hy)
  have hy_lt : y < d + 1 := hlt y hy
  exact ⟨hy1.1, by omega⟩

lemma validProfile_of_head_ne {d x : ℕ} {τ : List ℕ} (hx : x ≠ d + 1)
    (hv : IsValidProfile (d + 1) (x :: τ)) : IsValidProfile d (x :: τ) := by
  rcases hv with ⟨hpw, hmem⟩
  obtain ⟨hlt, _⟩ := List.pairwise_cons.mp hpw
  have hx_le : x ≤ d := by
    have := (hmem x List.mem_cons_self).2
    omega
  refine ⟨hpw, fun z hz => ?_⟩
  have hz1 := hmem z hz
  rcases List.mem_cons.mp hz with rfl | hztl
  · exact ⟨hz1.1, hx_le⟩
  · have hzx : z < x := hlt z hztl
    exact ⟨hz1.1, by omega⟩

lemma two_le_two_pow {d : ℕ} (hd : 1 ≤ d) : 2 ≤ 2 ^ d := by
  cases d with
  | zero => omega
  | succ k =>
      have : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by omega)
      rw [pow_succ]
      omega

lemma pCode_le_of_nonempty :
    ∀ {D : ℕ} {σ : List ℕ}, σ ≠ [] → IsValidProfile D σ → pCode D σ ≤ 2 ^ D - 2
  | 0, [], hne, _ => absurd rfl hne
  | 0, x :: _, _, ⟨_, hmem⟩ => by
      have := hmem x List.mem_cons_self
      omega
  | d + 1, [], hne, _ => absurd rfl hne
  | d + 1, x :: τ, _, hv => by
      have hpow1 : 1 ≤ 2 ^ d := Nat.one_le_pow d 2 (by omega)
      have hpow2 : 2 ^ (d + 1) = 2 * 2 ^ d := by ring
      rw [pCode]
      split_ifs with hx hτ
      · omega
      · omega
      · have hv_d := validProfile_of_head_ne hx hv
        have ih := pCode_le_of_nonempty (List.cons_ne_nil x τ) hv_d
        have hd_pos : 1 ≤ d := by
          have hx1 := hv_d.2 x List.mem_cons_self
          omega
        have := two_le_two_pow hd_pos
        omega

lemma pCode_succ_of_valid {d : ℕ} {σ : List ℕ} (hne : σ ≠ []) (hv : IsValidProfile d σ) :
    pCode (d + 1) σ = 2 ^ d + pCode d σ := by
  cases σ with
  | nil => exact absurd rfl hne
  | cons x τ =>
      have hx_le : x ≤ d := (hv.2 x List.mem_cons_self).2
      have hx_ne : x ≠ d + 1 := by omega
      rw [pCode, if_neg hx_ne]

lemma pCode_add_of_valid {d : ℕ} :
    ∀ {D : ℕ} (_ : d ≤ D) {σ : List ℕ}, σ ≠ [] → IsValidProfile d σ →
      pCode D σ + 2 ^ d = 2 ^ D + pCode d σ := by
  intro D hdD
  induction D with
  | zero =>
      have : d = 0 := by omega
      subst this
      intro σ _ _
      change pCode 0 σ + 1 = 1 + pCode 0 σ
      omega
  | succ D ih =>
      rcases eq_or_lt_of_le hdD with rfl | hlt
      · intro σ _ _
        omega
      · intro σ hne hv
        have hvD : IsValidProfile D σ :=
          ⟨hv.1, fun z hz => ⟨(hv.2 z hz).1, (hv.2 z hz).2.trans (by omega)⟩⟩
        rw [pCode_succ_of_valid hne hvD]
        have ih1 := ih (by omega) hne hv
        have : 2 ^ (D + 1) = 2 * 2 ^ D := by ring
        omega

lemma pCode_inj :
    ∀ {D : ℕ} {σ₁ σ₂ : List ℕ}, IsValidProfile D σ₁ → IsValidProfile D σ₂ →
      pCode D σ₁ = pCode D σ₂ → σ₁ = σ₂
  | 0, [], [], _, _, _ => rfl
  | 0, x :: _, _, ⟨_, hmem⟩, _, _ => by have := hmem x List.mem_cons_self; omega
  | 0, _, x :: _, _, ⟨_, hmem⟩, _ => by have := hmem x List.mem_cons_self; omega
  | d + 1, σ₁, σ₂, hv₁, hv₂, heq => by
      have hpow1 : 1 ≤ 2 ^ d := Nat.one_le_pow d 2 (by omega)
      have hpow2 : 2 ^ (d + 1) = 2 * 2 ^ d := by ring
      cases σ₁ with
      | nil =>
          cases σ₂ with
          | nil => rfl
          | cons x₂ τ₂ =>
              have hle := pCode_le_of_nonempty (List.cons_ne_nil x₂ τ₂) hv₂
              change 2 ^ (d + 1) - 1 = pCode (d + 1) (x₂ :: τ₂) at heq
              omega
      | cons x₁ τ₁ =>
          cases σ₂ with
          | nil =>
              have hle := pCode_le_of_nonempty (List.cons_ne_nil x₁ τ₁) hv₁
              change pCode (d + 1) (x₁ :: τ₁) = 2 ^ (d + 1) - 1 at heq
              omega
          | cons x₂ τ₂ =>
              rw [pCode, pCode] at heq
              by_cases hx1 : x₁ = d + 1 <;> by_cases hx2 : x₂ = d + 1
              · rw [if_pos hx1, if_pos hx2] at heq
                subst hx1; subst hx2
                by_cases hτ1 : τ₁ = [] <;> by_cases hτ2 : τ₂ = []
                · subst hτ1; subst hτ2; rfl
                · rw [if_pos hτ1, if_neg hτ2] at heq
                  cases τ₂ with
                  | nil => exact absurd rfl hτ2
                  | cons y₂ ys₂ =>
                      have hv_tl2 := validProfile_tail_of_eq hv₂
                      have hd1 : 1 ≤ d := (hv_tl2.2 y₂ List.mem_cons_self).1.trans
                        (hv_tl2.2 y₂ List.mem_cons_self).2
                      have := two_le_two_pow hd1
                      omega
                · rw [if_neg hτ1, if_pos hτ2] at heq
                  cases τ₁ with
                  | nil => exact absurd rfl hτ1
                  | cons y₁ ys₁ =>
                      have hv_tl1 := validProfile_tail_of_eq hv₁
                      have hd1 : 1 ≤ d := (hv_tl1.2 y₁ List.mem_cons_self).1.trans
                        (hv_tl1.2 y₁ List.mem_cons_self).2
                      have := two_le_two_pow hd1
                      omega
                · rw [if_neg hτ1, if_neg hτ2] at heq
                  have hv_tl1 := validProfile_tail_of_eq hv₁
                  have hv_tl2 := validProfile_tail_of_eq hv₂
                  have hle1 := pCode_le_of_nonempty hτ1 hv_tl1
                  have hle2 := pCode_le_of_nonempty hτ2 hv_tl2
                  cases τ₁ with
                  | nil => exact absurd rfl hτ1
                  | cons y₁ ys₁ =>
                      have hd1 : 1 ≤ d := (hv_tl1.2 y₁ List.mem_cons_self).1.trans
                        (hv_tl1.2 y₁ List.mem_cons_self).2
                      have := two_le_two_pow hd1
                      have hpeq : pCode d (y₁ :: ys₁) = pCode d τ₂ := by omega
                      rw [pCode_inj hv_tl1 hv_tl2 hpeq]
              · rw [if_pos hx1, if_neg hx2] at heq
                split_ifs at heq <;> omega
              · rw [if_neg hx1, if_pos hx2] at heq
                split_ifs at heq <;> omega
              · rw [if_neg hx1, if_neg hx2] at heq
                have hv1' := validProfile_of_head_ne hx1 hv₁
                have hv2' := validProfile_of_head_ne hx2 hv₂
                have hpeq : pCode d (x₁ :: τ₁) = pCode d (x₂ :: τ₂) := by omega
                exact pCode_inj hv1' hv2' hpeq

/-- Lemma 5.7: Profile anti-monotonicity `H ⊆ K → pCode D (profile C K) ≤ pCode D (profile C H)`. -/
lemma pCode_profile_anti {X : Type*} {C : LanguageClass X} (hnb : nbDim C ⊤ < ⊤) :
    ∀ H K : Set X, H ∈ infiniteClosure C → K ∈ infiniteClosure C → H ⊆ K →
      pCode (nbDim C ⊤).toNat (profile C K) ≤ pCode (nbDim C ⊤).toNat (profile C H) := by
  have hvalid_at_rk : ∀ Z : Set X, Z ∈ infiniteClosure C → IsValidProfile (rk C Z) (profile C Z) := by
    intro Z hZ
    obtain ⟨hne, ⟨hpw, hmemD⟩, hhead⟩ := profile_valid hnb Z hZ
    refine ⟨hpw, fun x hx => ?_⟩
    cases hZprof : profile C Z with
    | nil => exact absurd hZprof hne
    | cons a as =>
        have ha : a = rk C Z := by
          rw [hZprof] at hhead
          exact Option.some.inj hhead
        rw [hZprof] at hx hpw
        rcases List.mem_cons.mp hx with rfl | hxtl
        · exact ⟨(hmemD x (hZprof ▸ List.mem_cons_self)).1, ha.le⟩
        · have hlt := (List.pairwise_cons.mp hpw).1 x hxtl
          exact ⟨(hmemD x (hZprof ▸ List.mem_cons_of_mem _ hxtl)).1, by omega⟩
  have key : ∀ r : ℕ, ∀ H K : Set X, H ∈ infiniteClosure C → K ∈ infiniteClosure C →
      rk C K = r → H ⊆ K →
      IsValidProfile r (profile C K) ∧ IsValidProfile r (profile C H) ∧
      pCode r (profile C K) ≤ pCode r (profile C H) := by
    intro r
    induction r using Nat.strong_induction_on with
    | _ r ih =>
        intro H K hH hK hrK hHK
        have hrH_le : rk C H ≤ r := hrK ▸ rk_mono hnb hH hK hHK
        have hvK : IsValidProfile r (profile C K) := hrK ▸ hvalid_at_rk K hK
        have hvH0 : IsValidProfile (rk C H) (profile C H) := hvalid_at_rk H hH
        have hvH : IsValidProfile r (profile C H) :=
          ⟨hvH0.1, fun x hx => ⟨(hvH0.2 x hx).1, (hvH0.2 x hx).2.trans hrH_le⟩⟩
        refine ⟨hvK, hvH, ?_⟩
        rcases r with _ | r'
        · have := rk_pos hnb hK; omega
        · rcases lt_or_eq_of_le hrH_le with hlt_r | hrH_eq
          · have hK_ub : pCode (r' + 1) (profile C K) ≤ 2 ^ r' - 1 := by
              rw [profile]
              split_ifs with hltK
              · have hne_cK := (profile_valid hnb _ (core_mem_infiniteClosure hnb hK)).1
                rw [pCode, if_pos hrK, if_neg hne_cK]
                have : 1 ≤ 2 ^ r' := Nat.one_le_pow r' 2 (by omega)
                omega
              · rw [pCode, if_pos hrK, if_pos rfl]
            have hvH_r' : IsValidProfile r' (profile C H) :=
              ⟨hvH0.1, fun x hx => ⟨(hvH0.2 x hx).1, (hvH0.2 x hx).2.trans (by omega)⟩⟩
            have hH_lb : 2 ^ r' ≤ pCode (r' + 1) (profile C H) := by
              rw [pCode_succ_of_valid (profile_valid hnb H hH).1 hvH_r']
              omega
            omega
          · have hcK_ic := core_mem_infiniteClosure hnb hK
            have hcH_ic := core_mem_infiniteClosure hnb hH
            have hc_sub : core C K ⊆ core C H := core_anti_of_rk_eq hHK (hrH_eq.trans hrK.symm)
            have hcK_le_cH : rk C (core C K) ≤ rk C (core C H) := rk_mono hnb hcK_ic hcH_ic hc_sub
            have hcH_le_r : rk C (core C H) ≤ r' + 1 := hrH_eq ▸ rk_mono hnb hcH_ic hH (core_subset hH)
            by_cases hltK : rk C (core C K) < rk C K <;> by_cases hltH : rk C (core C H) < rk C H
            · have hpK : profile C K = rk C K :: profile C (core C K) := by rw [profile, dif_pos hltK]
              have hpH : profile C H = rk C H :: profile C (core C H) := by rw [profile, dif_pos hltH]
              rw [hpK, hpH]
              have hr_cH : rk C (core C H) ≤ r' := by omega
              obtain ⟨hvcH0, hvcK0, hp_le⟩ :=
                ih (rk C (core C H)) (by omega) (core C K) (core C H) hcK_ic hcH_ic rfl hc_sub
              have hne_cK := (profile_valid hnb _ hcK_ic).1
              have hne_cH := (profile_valid hnb _ hcH_ic).1
              have hp_r' : pCode r' (profile C (core C H)) ≤ pCode r' (profile C (core C K)) := by
                have h1 := pCode_add_of_valid hr_cH hne_cH hvcH0
                have h2 := pCode_add_of_valid hr_cH hne_cK hvcK0
                omega
              have hvcK_r' : IsValidProfile r' (profile C (core C K)) :=
                ⟨hvcK0.1, fun x hx => ⟨(hvcK0.2 x hx).1, (hvcK0.2 x hx).2.trans hr_cH⟩⟩
              have hle_cK := pCode_le_of_nonempty hne_cK hvcK_r'
              rw [pCode, if_pos hrK, if_neg hne_cK, pCode, if_pos hrH_eq, if_neg hne_cH]
              omega
            · have hpK : profile C K = rk C K :: profile C (core C K) := by rw [profile, dif_pos hltK]
              have hpH : profile C H = [rk C H] := by rw [profile, dif_neg hltH]
              rw [hpK, hpH]
              have hne_cK := (profile_valid hnb _ hcK_ic).1
              rw [pCode, if_pos hrK, if_neg hne_cK, pCode, if_pos hrH_eq, if_pos rfl]
              have : 1 ≤ 2 ^ r' := Nat.one_le_pow r' 2 (by omega)
              omega
            · omega
            · have hpK : profile C K = [rk C K] := by rw [profile, dif_neg hltK]
              have hpH : profile C H = [rk C H] := by rw [profile, dif_neg hltH]
              rw [hpK, hpH, hrK, hrH_eq]
  intro H K hH hK hHK
  obtain ⟨hvK, hvH, hle⟩ := key (rk C K) H K hH hK rfl hHK
  have hrK_D : rk C K ≤ (nbDim C ⊤).toNat := rk_le_nbDim hnb hK
  have h1 := pCode_add_of_valid hrK_D (profile_valid hnb K hK).1 hvK
  have h2 := pCode_add_of_valid hrK_D (profile_valid hnb H hH).1 hvH
  omega

/-- Section 5.3: Augmented profile in `Fin (2 ^ (d + 1))` and augmented iterated core. -/
noncomputable def barProfile {X : Type*} (C : LanguageClass X) (hnb : nbDim C ⊤ < ⊤)
    (K : Set X) : Fin (2 ^ ((nbDim C ⊤).toNat + 1)) :=
  if K = ∅ then
    ⟨2 ^ ((nbDim C ⊤).toNat + 1) - 1, by
      have : 1 ≤ 2 ^ ((nbDim C ⊤).toNat + 1) := Nat.one_le_pow _ 2 (by omega)
      omega⟩
  else if hK : K ∈ infiniteClosure C then
    ⟨pCode ((nbDim C ⊤).toNat + 1) (profile C K), by
      have hv : IsValidProfile ((nbDim C ⊤).toNat + 1) (profile C K) := by
        obtain ⟨_, ⟨hpw, hmem⟩, _⟩ := profile_valid hnb K hK
        exact ⟨hpw, fun x hx => ⟨(hmem x hx).1, (hmem x hx).2.trans (by omega)⟩⟩
      have hle := pCode_le_of_nonempty (profile_valid hnb K hK).1 hv
      have : 2 ≤ 2 ^ ((nbDim C ⊤).toNat + 1) := by
        calc 2 = 2 ^ 1 := by ring
          _ ≤ 2 ^ ((nbDim C ⊤).toNat + 1) := Nat.pow_le_pow_right (by omega) (by omega)
      omega⟩
  else
    ⟨2 ^ (nbDim C ⊤).toNat - 1, by
      have : 1 ≤ 2 ^ (nbDim C ⊤).toNat := Nat.one_le_pow _ 2 (by omega)
      have : 2 ^ ((nbDim C ⊤).toNat + 1) = 2 * 2 ^ (nbDim C ⊤).toNat := by ring
      omega⟩

noncomputable def barCore {X : Type*} (C : LanguageClass X) (K : Set X) : Set X :=
  if K ∈ infiniteClosure C then iterCore C K else Set.univ

lemma barCore_infinite {X : Type} {C : LanguageClass X} (hnb : nbDim C ⊤ < ⊤) (K : Set X) :
    (barCore C K).Infinite := by
  unfold barCore
  split_ifs with hK
  · exact (iterCore_mem_infiniteClosure hnb K hK).1.1
  · have : Infinite X := infinite_X_of_languageClass C
    exact Set.infinite_univ

/-- Valid range of `Q_t(S)`: `infiniteClosure C ∪ {∅, Set.univ}`. -/
def IsValidQ {X : Type*} (C : LanguageClass X) (K : Set X) : Prop :=
  K ∈ infiniteClosure C ∨ K = ∅ ∨ K = Set.univ

/-- Lemma 5.12: Monotonicity and core stability of `(barProfile, barCore)` on `IsValidQ`. -/
lemma barProfile_anti {X : Type} {C : LanguageClass X} (hnb : nbDim C ⊤ < ⊤)
    {H K : Set X} (hH : IsValidQ C H) (hK : IsValidQ C K) (hHK : H ⊆ K) :
    barProfile C hnb K ≤ barProfile C hnb H := by
  rw [Fin.le_iff_val_le_val]
  unfold barProfile
  have hd1 : 1 ≤ 2 ^ (nbDim C ⊤).toNat := Nat.one_le_pow _ 2 (by omega)
  have hd2 : 2 ^ ((nbDim C ⊤).toNat + 1) = 2 * 2 ^ (nbDim C ⊤).toNat := by ring
  split_ifs with hK0 hH0 hH_ic hK_ic hH0' hH_ic3 hH0'' hH_ic4
  · exact le_refl _
  · subst hK0; exact absurd (Set.subset_empty_iff.mp hHK) hH0
  · subst hK0; exact absurd (Set.subset_empty_iff.mp hHK) hH0
  · simp only
    have hv := (profile_valid hnb K hK_ic).2.1
    have hv' : IsValidProfile ((nbDim C ⊤).toNat + 1) (profile C K) :=
      ⟨hv.1, fun x hx => ⟨(hv.2 x hx).1, (hv.2 x hx).2.trans (by omega)⟩⟩
    have hle := pCode_le_of_nonempty (profile_valid hnb K hK_ic).1 hv'
    have hd_ge1 : 1 ≤ (nbDim C ⊤).toNat := (rk_pos hnb hK_ic).trans (rk_le_nbDim hnb hK_ic)
    have := two_le_two_pow hd_ge1
    omega
  · simp only
    rw [pCode_succ_of_valid (profile_valid hnb K hK_ic).1 (profile_valid hnb K hK_ic).2.1,
        pCode_succ_of_valid (profile_valid hnb H hH_ic3).1 (profile_valid hnb H hH_ic3).2.1]
    have := pCode_profile_anti hnb H K hH_ic3 hK_ic hHK
    omega
  · rcases hH with h1 | h2 | rfl
    · exact absurd h1 hH_ic3
    · exact absurd h2 hH0'
    · have : K = Set.univ := Set.univ_subset_iff.mp hHK
      subst this
      exact absurd hK_ic hH_ic3
  · simp only; omega
  · simp only
    rw [pCode_succ_of_valid (profile_valid hnb H hH_ic4).1 (profile_valid hnb H hH_ic4).2.1]
    omega
  · exact le_refl _

lemma barCore_eq_of_barProfile_eq {X : Type} {C : LanguageClass X} (hnb : nbDim C ⊤ < ⊤)
    {H K : Set X} (hHK : H ⊆ K)
    (heq : barProfile C hnb H = barProfile C hnb K) :
    barCore C H = barCore C K := by
  have hval : (barProfile C hnb H).val = (barProfile C hnb K).val := congrArg Fin.val heq
  unfold barProfile at hval
  unfold barCore
  have hd1 : 1 ≤ 2 ^ (nbDim C ⊤).toNat := Nat.one_le_pow _ 2 (by omega)
  have hd2 : 2 ^ ((nbDim C ⊤).toNat + 1) = 2 * 2 ^ (nbDim C ⊤).toNat := by ring
  have hnot_empty_ic : ∀ Z : Set X, Z ∈ infiniteClosure C → Z ≠ ∅ :=
    fun Z hZ h0 => by subst h0; exact Set.not_infinite.mpr Set.finite_empty hZ.1
  have hrange_ic : ∀ Z : Set X, Z ∈ infiniteClosure C →
      2 ^ (nbDim C ⊤).toNat ≤ pCode ((nbDim C ⊤).toNat + 1) (profile C Z) ∧
      pCode ((nbDim C ⊤).toNat + 1) (profile C Z) ≤ 2 ^ ((nbDim C ⊤).toNat + 1) - 2 := by
    intro Z hZ
    have hne := (profile_valid hnb Z hZ).1
    have hv := (profile_valid hnb Z hZ).2.1
    have h1 := pCode_succ_of_valid hne hv
    have hv' : IsValidProfile ((nbDim C ⊤).toNat + 1) (profile C Z) :=
      ⟨hv.1, fun x hx => ⟨(hv.2 x hx).1, (hv.2 x hx).2.trans (by omega)⟩⟩
    have h2 := pCode_le_of_nonempty hne hv'
    have hd_ge1 : 1 ≤ (nbDim C ⊤).toNat := (rk_pos hnb hZ).trans (rk_le_nbDim hnb hZ)
    have := two_le_two_pow hd_ge1
    omega
  split_ifs with hH_ic hK_ic hK_ic2
  · have hH0 : H ≠ ∅ := hnot_empty_ic H hH_ic
    have hK0 : K ≠ ∅ := hnot_empty_ic K hK_ic
    simp only [hH0, hK0, hH_ic, hK_ic, ↓reduceIte, ↓reduceDIte] at hval
    have hvH : IsValidProfile ((nbDim C ⊤).toNat + 1) (profile C H) := by
      have hv := (profile_valid hnb H hH_ic).2.1
      exact ⟨hv.1, fun x hx => ⟨(hv.2 x hx).1, (hv.2 x hx).2.trans (by omega)⟩⟩
    have hvK : IsValidProfile ((nbDim C ⊤).toNat + 1) (profile C K) := by
      have hv := (profile_valid hnb K hK_ic).2.1
      exact ⟨hv.1, fun x hx => ⟨(hv.2 x hx).1, (hv.2 x hx).2.trans (by omega)⟩⟩
    exact iterCore_eq_of_profile_eq hnb H K hH_ic hK_ic hHK (pCode_inj hvH hvK hval)
  · have hH0 : H ≠ ∅ := hnot_empty_ic H hH_ic
    obtain ⟨hlo, hhi⟩ := hrange_ic H hH_ic
    by_cases hK0 : K = ∅
    · simp only [hH0, hK0, hH_ic, ↓reduceIte, ↓reduceDIte] at hval; omega
    · simp only [hH0, hK0, hH_ic, hK_ic, ↓reduceIte, ↓reduceDIte] at hval; omega
  · have hK0 : K ≠ ∅ := hnot_empty_ic K hK_ic2
    obtain ⟨hlo, hhi⟩ := hrange_ic K hK_ic2
    by_cases hH0 : H = ∅
    · simp only [hH0, hK0, hK_ic2, ↓reduceIte, ↓reduceDIte] at hval; omega
    · simp only [hH0, hK0, hH_ic, hK_ic2, ↓reduceIte, ↓reduceDIte] at hval; omega
  · rfl

end Combinatorics

/-! ### Part 3: Upper Bound (`closureDim C < ⊤ ∧ nbDim C ⊤ < ⊤ → PrivatelyUniformlyGeneratable C`) -/

section UpperBound

lemma infinite_closure_of_card_gt {X : Type*} {C : LanguageClass X}
    (hc : closureSizeSup C < ⊤) {T : Finset X}
    (hcard : (closureSizeSup C).toNat < T.card)
    (hreal : ∃ L ∈ C.languages, (↑T : Set X) ⊆ L) :
    closure C (↑T : Set X) ∈ infiniteClosure C := by
  have hne : T.Nonempty := Finset.card_pos.mp (by omega)
  have hinf : (closure C (↑T : Set X)).Infinite := by
    by_contra hnot
    have hfin : (closure C (↑T : Set X)).Finite := Set.not_infinite.mp hnot
    have hle : (T.card : ℕ∞) ≤ closureSizeSup C := by
      unfold closureSizeSup
      exact le_iSup₂_of_le T hne (le_iSup₂_of_le hreal hfin (le_refl _))
    rw [← ENat.natCast_toNat hc.ne] at hle
    have := Nat.cast_le.mp hle
    omega
  obtain ⟨L₀, hL₀, hTL₀⟩ := hreal
  exact ⟨hinf, ⟨{L ∈ C.languages | (↑T : Set X) ⊆ L}, ⟨L₀, hL₀, hTL₀⟩,
    fun _ h => h.1, rfl⟩⟩

/-- Realizable subsets of `support S` obtained by omitting `t` elements. -/
def RSet {X : Type*} (C : LanguageClass X) {n : ℕ} (t : ℕ) (S : Fin n → X) : Set (Finset X) :=
  {T : Finset X | T ⊆ support S ∧ T.card + t = (support S).card ∧
    ∃ L ∈ C.languages, (↑T : Set X) ⊆ L}

/-- Definition 5.9: Robust closure `Q_t(S)` using parameters `c` and `h`. -/
noncomputable def robustQ {X : Type*} (C : LanguageClass X) (c h t : ℕ)
    {n : ℕ} (S : Fin n → X) : Set X :=
  if (support S).card ≤ c + h * t then ∅
  else if (RSet C t S).Nonempty then
    ⋂₀ ((fun T : Finset X => closure C (↑T : Set X)) '' RSet C t S)
  else Set.univ

/-- Lemma 5.10: When `|support S| > c + h * t` and `RSet C t S` is nonempty, `robustQ ∈ infiniteClosure C`. -/
lemma robustQ_mem_infiniteClosure {X : Type*} {C : LanguageClass X}
    (hc : closureSizeSup C < ⊤) (hnb : nbDim C ⊤ < ⊤) {t n : ℕ} {S : Fin n → X}
    (hcard : (closureSizeSup C).toNat + ((nbDim C ⊤).toNat + 1) * t < (support S).card)
    (hne : (RSet C t S).Nonempty) :
    robustQ C (closureSizeSup C).toNat ((nbDim C ⊤).toNat + 1) t S ∈ infiniteClosure C := by
  set c := (closureSizeSup C).toNat
  set h := (nbDim C ⊤).toNat + 1
  have hnot_le : ¬ ((support S).card ≤ c + h * t) := by omega
  unfold robustQ
  rw [if_neg hnot_le, if_pos hne]
  let Fam : Set (Set X) := (fun T : Finset X => closure C (↑T : Set X)) '' RSet C t S
  obtain ⟨T₀, hT₀⟩ := hne
  have hFam_ne : Fam.Nonempty := ⟨closure C ↑T₀, T₀, hT₀, rfl⟩
  have hFam_ic : Fam ⊆ infiniteClosure C := by
    rintro _ ⟨T, ⟨_, hTcard, hTreal⟩, rfl⟩
    have ht_le : t ≤ h * t := Nat.le_mul_of_pos_left t (by omega)
    exact infinite_closure_of_card_gt hc (by omega) hTreal
  have hinf : (⋂₀ Fam).Infinite := by
    by_contra hnot
    have hfin : (⋂₀ Fam).Finite := Set.not_infinite.mp hnot
    obtain ⟨G, hGne, hGF, hGcard, hGfin⟩ := helly_infiniteClosure hnb hFam_ne hFam_ic hfin
    choose witness hw_mem hw_eq using fun (x : {K // K ∈ G}) => hGF x.2
    let D : Finset X := G.attach.biUnion fun x => support S \ witness x
    have hD_card : D.card ≤ h * t := by
      calc D.card
          ≤ ∑ x ∈ G.attach, (support S \ witness x).card := Finset.card_biUnion_le
        _ = ∑ _x ∈ G.attach, t := by
            refine Finset.sum_congr rfl fun x _ => ?_
            obtain ⟨hsub, htc, _⟩ := hw_mem x
            have hsdiff := Finset.card_sdiff_add_card_eq_card hsub
            omega
        _ = G.attach.card * t := by rw [Finset.sum_const, smul_eq_mul]
        _ = G.card * t := by rw [Finset.card_attach]
        _ ≤ h * t := Nat.mul_le_mul_right t hGcard
    set U : Finset X := support S \ D
    have hD_sub : D ⊆ support S := by
      intro z hz
      rcases Finset.mem_biUnion.mp hz with ⟨x, _, hzx⟩
      exact (Finset.mem_sdiff.mp hzx).1
    have hU_card : c < U.card := by
      have hsdiff : U.card + D.card = (support S).card := Finset.card_sdiff_add_card_eq_card hD_sub
      have hcard' : c + h * t < (support S).card := hcard
      omega
    have hU_sub_witness : ∀ x : {K // K ∈ G}, U ⊆ witness x := by
      intro x z hz
      obtain ⟨hzS, hzD⟩ := Finset.mem_sdiff.mp hz
      by_contra hzw
      apply hzD
      exact Finset.mem_biUnion.mpr ⟨x, Finset.mem_attach G x, Finset.mem_sdiff.mpr ⟨hzS, hzw⟩⟩
    obtain ⟨K₀, hK₀⟩ := hGne
    have hU_real : ∃ L ∈ C.languages, (↑U : Set X) ⊆ L := by
      obtain ⟨_, _, L, hL, hwL⟩ := hw_mem ⟨K₀, hK₀⟩
      exact ⟨L, hL, (Finset.coe_subset.mpr (hU_sub_witness ⟨K₀, hK₀⟩)).trans hwL⟩
    have hU_ic := infinite_closure_of_card_gt hc hU_card hU_real
    have hU_sub_G : closure C (↑U : Set X) ⊆ ⋂₀ (↑G : Set (Set X)) := by
      intro z hz K hKG
      have hKeq : closure C (↑(witness ⟨K, hKG⟩) : Set X) = K := hw_eq ⟨K, hKG⟩
      rw [← hKeq]
      exact closure_mono C (Finset.coe_subset.mpr (hU_sub_witness ⟨K, hKG⟩)) hz
    exact hU_ic.1 (hGfin.subset hU_sub_G)
  exact sInter_mem_infiniteClosure C hFam_ne hFam_ic hinf

lemma robustQ_valid {X : Type*} {C : LanguageClass X}
    (hc : closureSizeSup C < ⊤) (hnb : nbDim C ⊤ < ⊤) (t : ℕ) {n : ℕ} (S : Fin n → X) :
    IsValidQ C (robustQ C (closureSizeSup C).toNat ((nbDim C ⊤).toNat + 1) t S) := by
  by_cases h1 : (support S).card ≤ (closureSizeSup C).toNat + ((nbDim C ⊤).toNat + 1) * t
  · right; left
    unfold robustQ; exact if_pos h1
  · by_cases h2 : (RSet C t S).Nonempty
    · left
      exact robustQ_mem_infiniteClosure hc hnb (by omega) h2
    · right; right
      unfold robustQ; rw [if_neg h1, if_neg h2]

lemma card_support_sdiff_le_one {X : Type*} {n : ℕ} {S S' : Fin n → X} (h : Near S S') :
    (support S \ support S').card ≤ 1 := by
  rcases h with rfl | ⟨i₀, _, hrest⟩
  · simp
  · have hsub : support S \ support S' ⊆ {S i₀} := by
      intro x hx
      obtain ⟨hxS, hxS'⟩ := Finset.mem_sdiff.mp hx
      unfold support at hxS hxS'
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hxS
      by_cases hj : j = i₀
      · subst hj; exact Finset.mem_singleton_self _
      · exfalso; apply hxS'
        rw [hrest j hj]
        exact Finset.mem_image_of_mem S' (Finset.mem_univ j)
    exact (Finset.card_le_card hsub).trans (by simp)

lemma card_support_le_succ_of_near {X : Type*} {n : ℕ} {S S' : Fin n → X} (h : Near S S') :
    (support S).card ≤ (support S').card + 1 := by
  have h1 := Finset.card_sdiff_add_card_inter (support S) (support S')
  have h2 : (support S ∩ support S').card ≤ (support S').card :=
    Finset.card_le_card Finset.inter_subset_right
  have h3 := card_support_sdiff_le_one h
  omega

/-- Lemma 5.11: Interlacing of `robustQ` across `Near` datasets (`h ≥ 1`). -/
lemma robustQ_interlace {X : Type*} {C : LanguageClass X} {c h t n : ℕ} (hh : 1 ≤ h)
    {S S' : Fin n → X} (hnear : Near S S') :
    robustQ C c h (t + 1) S ⊆ robustQ C c h t S' := by
  by_cases hleS : (support S).card ≤ c + h * (t + 1)
  · unfold robustQ
    rw [if_pos hleS]
    exact Set.empty_subset _
  · have hcard_le := card_support_le_succ_of_near hnear
    have hmul : h * (t + 1) = h * t + h := Nat.mul_succ h t
    have hnot_leS' : ¬ ((support S').card ≤ c + h * t) := by omega
    by_cases hneS' : (RSet C t S').Nonempty
    · have hRHS : robustQ C c h t S' =
          ⋂₀ ((fun T : Finset X => closure C (↑T : Set X)) '' RSet C t S') := by
        unfold robustQ; rw [if_neg hnot_leS', if_pos hneS']
      rw [hRHS]
      rintro x hx _ ⟨T', hT', rfl⟩
      obtain ⟨hT'sub, hT'card, L, hL, hT'L⟩ := hT'
      have hsdiff_le : (support S \ T').card ≤ t + 1 := by
        have hsub : support S \ T' ⊆ (support S \ support S') ∪ (support S' \ T') := by
          intro z hz
          obtain ⟨hzS, hzT'⟩ := Finset.mem_sdiff.mp hz
          by_cases hzS' : z ∈ support S'
          · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hzS', hzT'⟩)
          · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hzS, hzS'⟩)
        have hc1 := Finset.card_le_card hsub
        have hc2 := Finset.card_union_le (support S \ support S') (support S' \ T')
        have hc3 := card_support_sdiff_le_one hnear
        have hc4 := Finset.card_sdiff_add_card_eq_card hT'sub
        omega
      have hinter_ge : (support S).card - (t + 1) ≤ (support S ∩ T').card := by
        have hpart := Finset.card_sdiff_add_card_inter (support S) T'
        omega
      have ht1_lt : t + 1 ≤ (support S).card := by
        have : t + 1 ≤ h * (t + 1) := Nat.le_mul_of_pos_left (t + 1) hh
        omega
      obtain ⟨T, hT_sub_inter, hT_card⟩ :=
        Finset.exists_subset_card_eq hinter_ge
      have hT_mem : T ∈ RSet C (t + 1) S := by
        refine ⟨hT_sub_inter.trans Finset.inter_subset_left, by omega, ⟨L, hL, ?_⟩⟩
        exact (Finset.coe_subset.mpr (hT_sub_inter.trans Finset.inter_subset_right)).trans hT'L
      have hneS : (RSet C (t + 1) S).Nonempty := ⟨T, hT_mem⟩
      have hLHS : robustQ C c h (t + 1) S =
          ⋂₀ ((fun U : Finset X => closure C (↑U : Set X)) '' RSet C (t + 1) S) := by
        unfold robustQ; rw [if_neg hleS, if_pos hneS]
      rw [hLHS] at hx
      have hxT : x ∈ closure C (↑T : Set X) := hx _ ⟨T, hT_mem, rfl⟩
      exact closure_mono C (Finset.coe_subset.mpr (hT_sub_inter.trans Finset.inter_subset_right)) hxT
    · unfold robustQ
      rw [if_neg hnot_leS', if_neg hneS']
      exact Set.subset_univ _

lemma robustQ_anti {X : Type*} {C : LanguageClass X} {c h n : ℕ} (hh : 1 ≤ h)
    (S : Fin n → X) : ∀ {t₁ t₂ : ℕ}, t₁ ≤ t₂ → robustQ C c h t₂ S ⊆ robustQ C c h t₁ S := by
  intro t₁ t₂ hle
  induction t₂ with
  | zero =>
      have : t₁ = 0 := by omega
      subst this; exact Set.Subset.rfl
  | succ t₂ ih =>
      rcases eq_or_lt_of_le hle with rfl | hlt
      · exact Set.Subset.rfl
      · exact (robustQ_interlace hh (Or.inl rfl)).trans (ih (by omega))

/-- Profile sequence, block sets, block lengths, and block cores for `t ∈ Fin N`. -/
noncomputable def profAt {X : Type} (C : LanguageClass X) (hnb : nbDim C ⊤ < ⊤)
    (N : ℕ) {n : ℕ} (S : Fin n → X) (t : Fin N) : Fin (2 ^ ((nbDim C ⊤).toNat + 1)) :=
  barProfile C hnb (robustQ C (closureSizeSup C).toNat ((nbDim C ⊤).toNat + 1) t.val S)

lemma profAt_mono {X : Type} {C : LanguageClass X} (hc : closureSizeSup C < ⊤)
    (hnb : nbDim C ⊤ < ⊤) {N n : ℕ} (S : Fin n → X) {t₁ t₂ : Fin N} (hle : t₁ ≤ t₂) :
    profAt C hnb N S t₁ ≤ profAt C hnb N S t₂ :=
  barProfile_anti hnb (robustQ_valid hc hnb t₂.val S) (robustQ_valid hc hnb t₁.val S)
    (robustQ_anti (by omega) S (Fin.le_iff_val_le_val.mp hle))

lemma profAt_interlace {X : Type} {C : LanguageClass X} (hc : closureSizeSup C < ⊤)
    (hnb : nbDim C ⊤ < ⊤) {N n : ℕ} {S S' : Fin n → X} (hnear : Near S S')
    {t t' : Fin N} (ht : t.val = t'.val + 1) :
    profAt C hnb N S' t' ≤ profAt C hnb N S t := by
  unfold profAt
  rw [ht]
  exact barProfile_anti hnb
    (robustQ_valid hc hnb (t'.val + 1) S) (robustQ_valid hc hnb t'.val S')
    (robustQ_interlace (by omega) hnear)

noncomputable def blockSet {X : Type} (C : LanguageClass X) (hnb : nbDim C ⊤ < ⊤)
    (N : ℕ) {n : ℕ} (S : Fin n → X) (σ : Fin (2 ^ ((nbDim C ⊤).toNat + 1))) : Finset (Fin N) :=
  Finset.univ.filter fun t : Fin N => profAt C hnb N S t = σ

noncomputable def blockLen {X : Type} (C : LanguageClass X) (hnb : nbDim C ⊤ < ⊤)
    (N : ℕ) {n : ℕ} (S : Fin n → X) (σ : Fin (2 ^ ((nbDim C ⊤).toNat + 1))) : ℕ :=
  (blockSet C hnb N S σ).card

noncomputable def prefixCount {X : Type} (C : LanguageClass X) (hnb : nbDim C ⊤ < ⊤)
    (N : ℕ) {n : ℕ} (S : Fin n → X) (k : ℕ) : ℕ :=
  (Finset.univ.filter fun t : Fin N => (profAt C hnb N S t).val < k).card

lemma prefixCount_succ {X : Type} {C : LanguageClass X} (hnb : nbDim C ⊤ < ⊤)
    (N : ℕ) {n : ℕ} (S : Fin n → X) (σ : Fin (2 ^ ((nbDim C ⊤).toNat + 1))) :
    prefixCount C hnb N S (σ.val + 1) = prefixCount C hnb N S σ.val + blockLen C hnb N S σ := by
  unfold prefixCount blockLen blockSet
  have hunion : (Finset.univ.filter fun t : Fin N => (profAt C hnb N S t).val < σ.val + 1) =
      (Finset.univ.filter fun t : Fin N => (profAt C hnb N S t).val < σ.val) ∪
      (Finset.univ.filter fun t : Fin N => profAt C hnb N S t = σ) := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Fin.ext_iff]
    omega
  have hdisj : Disjoint
      (Finset.univ.filter fun t : Fin N => (profAt C hnb N S t).val < σ.val)
      (Finset.univ.filter fun t : Fin N => profAt C hnb N S t = σ) := by
    rw [Finset.disjoint_filter]
    intro t _ hlt heq
    rw [heq] at hlt
    exact Nat.lt_irrefl _ hlt
  rw [hunion, Finset.card_union_of_disjoint hdisj]

lemma prefixCount_near_le {X : Type} {C : LanguageClass X} (hc : closureSizeSup C < ⊤)
    (hnb : nbDim C ⊤ < ⊤) {N n : ℕ} (hN : 1 ≤ N)
    {S S' : Fin n → X} (hnear : Near S S') (k : ℕ) :
    prefixCount C hnb N S k ≤ prefixCount C hnb N S' k + 1 := by
  unfold prefixCount
  set A := Finset.univ.filter fun t : Fin N => (profAt C hnb N S t).val < k
  set A' := Finset.univ.filter fun t : Fin N => (profAt C hnb N S' t).val < k
  let z₀ : Fin N := ⟨0, by omega⟩
  let predF : Fin N → Fin N := fun t => ⟨t.val - 1, by omega⟩
  have herase_le : (A.erase z₀).card ≤ A'.card := by
    refine Finset.card_le_card_of_injOn predF ?_ ?_
    · intro t ht
      obtain ⟨ht_ne, htA⟩ := Finset.mem_erase.mp ( Finset.mem_coe.mp ht )
      have ht_pos : 1 ≤ t.val := by
        have : t.val ≠ 0 := fun h0 => ht_ne (Fin.ext h0)
        omega
      have hlt_k : (profAt C hnb N S t).val < k := (Finset.mem_filter.mp htA).2
      have hle_p : profAt C hnb N S' (predF t) ≤ profAt C hnb N S t :=
        profAt_interlace hc hnb hnear (by dsimp [predF]; omega)
      have hlt' : (profAt C hnb N S' (predF t)).val < k :=
        lt_of_le_of_lt (Fin.le_iff_val_le_val.mp hle_p) hlt_k
      exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt'⟩)
    · intro t₁ ht₁ t₂ ht₂ heq
      obtain ⟨ht₁_ne, _⟩ := Finset.mem_erase.mp (Finset.mem_coe.mp ht₁)
      obtain ⟨ht₂_ne, _⟩ := Finset.mem_erase.mp (Finset.mem_coe.mp ht₂)
      have h1 : t₁.val ≠ 0 := fun h0 => ht₁_ne (Fin.ext h0)
      have h2 : t₂.val ≠ 0 := fun h0 => ht₂_ne (Fin.ext h0)
      have hv : t₁.val - 1 = t₂.val - 1 := congrArg Fin.val heq
      exact Fin.ext (by omega)
  have hA_le : A.card ≤ (A.erase z₀).card + 1 := by
    by_cases hz : z₀ ∈ A
    · have := Finset.card_erase_add_one hz
      omega
    · rw [Finset.erase_eq_of_notMem hz]
      omega
  omega

/-- Lemma 5.15 (Part 1): Sensitivity `≤ 2` of `blockLen`. -/
lemma blockLen_near_le {X : Type} {C : LanguageClass X} (hc : closureSizeSup C < ⊤)
    (hnb : nbDim C ⊤ < ⊤) {N n : ℕ} (hN : 1 ≤ N)
    {S S' : Fin n → X} (hnear : Near S S') (σ : Fin (2 ^ ((nbDim C ⊤).toNat + 1))) :
    blockLen C hnb N S σ ≤ blockLen C hnb N S' σ + 2 := by
  have h1 := prefixCount_succ (hnb := hnb) N S σ
  have h2 := prefixCount_succ (hnb := hnb) N S' σ
  have h3 := prefixCount_near_le hc hnb hN hnear (σ.val + 1)
  have h4 := prefixCount_near_le hc hnb hN (near_symm hnear) σ.val
  omega

noncomputable def blockCore {X : Type} (C : LanguageClass X) (hnb : nbDim C ⊤ < ⊤)
    (N : ℕ) {n : ℕ} (S : Fin n → X) (σ : Fin (2 ^ ((nbDim C ⊤).toNat + 1))) : Set X :=
  if hne : (blockSet C hnb N S σ).Nonempty then
    barCore C (robustQ C (closureSizeSup C).toNat ((nbDim C ⊤).toNat + 1)
      ((blockSet C hnb N S σ).min' hne).val S)
  else
    Set.univ

lemma blockCore_eq_at {X : Type} {C : LanguageClass X} (hnb : nbDim C ⊤ < ⊤)
    {N n : ℕ} {S : Fin n → X} {σ : Fin (2 ^ ((nbDim C ⊤).toNat + 1))}
    {t : Fin N} (ht : profAt C hnb N S t = σ) :
    blockCore C hnb N S σ =
      barCore C (robustQ C (closureSizeSup C).toNat ((nbDim C ⊤).toNat + 1) t.val S) := by
  have hmem : t ∈ blockSet C hnb N S σ := Finset.mem_filter.mpr ⟨Finset.mem_univ t, ht⟩
  have hne : (blockSet C hnb N S σ).Nonempty := ⟨t, hmem⟩
  unfold blockCore
  rw [dif_pos hne]
  set t₀ := (blockSet C hnb N S σ).min' hne
  have ht₀_le : t₀ ≤ t := Finset.min'_le _ t hmem
  have ht₀_prof : profAt C hnb N S t₀ = σ :=
    (Finset.mem_filter.mp (Finset.min'_mem _ hne)).2
  have hsub : robustQ C (closureSizeSup C).toNat ((nbDim C ⊤).toNat + 1) t.val S ⊆
      robustQ C (closureSizeSup C).toNat ((nbDim C ⊤).toNat + 1) t₀.val S :=
    robustQ_anti (by omega) S (Fin.le_iff_val_le_val.mp ht₀_le)
  exact (barCore_eq_of_barProfile_eq hnb hsub (ht.trans ht₀_prof.symm)).symm

/-- Lemma 5.15 (Part 2): Stability of `blockCore` when `blockLen ≥ 3`. -/
lemma blockCore_eq_of_ge_three {X : Type} {C : LanguageClass X} (hc : closureSizeSup C < ⊤)
    (hnb : nbDim C ⊤ < ⊤) {N n : ℕ} (hN : 1 ≤ N)
    {S S' : Fin n → X} (hnear : Near S S') {σ : Fin (2 ^ ((nbDim C ⊤).toNat + 1))}
    (hlen : 3 ≤ blockLen C hnb N S σ) :
    1 ≤ blockLen C hnb N S' σ ∧ blockCore C hnb N S σ = blockCore C hnb N S' σ := by
  have hlen' : 1 ≤ blockLen C hnb N S' σ := by
    have := blockLen_near_le hc hnb hN hnear σ
    omega
  refine ⟨hlen', ?_⟩
  have hne : (blockSet C hnb N S σ).Nonempty := Finset.card_pos.mp (Nat.lt_of_lt_of_le (by omega : 0 < 3) hlen)
  have hne' : (blockSet C hnb N S' σ).Nonempty := Finset.card_pos.mp hlen'
  let t_min := (blockSet C hnb N S σ).min' hne
  let t_max := (blockSet C hnb N S σ).max' hne
  obtain ⟨t', ht'_mem⟩ := hne'
  have ht'_prof : profAt C hnb N S' t' = σ := (Finset.mem_filter.mp ht'_mem).2
  have htmin_prof : profAt C hnb N S t_min = σ :=
    (Finset.mem_filter.mp (Finset.min'_mem _ hne)).2
  have htmax_prof : profAt C hnb N S t_max = σ :=
    (Finset.mem_filter.mp (Finset.max'_mem _ hne)).2
  -- Show `t_min.val + 2 ≤ t_max.val` since `(blockSet C hnb N S σ).card ≥ 3`.
  have hgap : t_min.val + 2 ≤ t_max.val := by
    have hcard_le : (blockSet C hnb N S σ).card ≤ (Finset.Icc t_min.val t_max.val).card := by
      refine Finset.card_le_card_of_injOn Fin.val ?_ fun _ _ _ _ h => Fin.ext h
      intro t ht
      have htB := Finset.mem_coe.mp ht
      have h1 : t_min.val ≤ t.val := Fin.le_iff_val_le_val.mp (Finset.min'_le _ t htB)
      have h2 : t.val ≤ t_max.val := Fin.le_iff_val_le_val.mp (Finset.le_max' _ t htB)
      exact Finset.mem_coe.mpr (Finset.mem_Icc.mpr ⟨h1, h2⟩)
    rw [Nat.card_Icc] at hcard_le
    change 3 ≤ (blockSet C hnb N S σ).card at hlen
    omega
  by_cases hcmp : t_min.val + 1 ≤ t'.val
  · have hsub1 : robustQ C (closureSizeSup C).toNat ((nbDim C ⊤).toNat + 1) t'.val S' ⊆
        robustQ C (closureSizeSup C).toNat ((nbDim C ⊤).toNat + 1) (t_min.val + 1) S' :=
      robustQ_anti (by omega) S' hcmp
    have hsub2 : robustQ C (closureSizeSup C).toNat ((nbDim C ⊤).toNat + 1) (t_min.val + 1) S' ⊆
        robustQ C (closureSizeSup C).toNat ((nbDim C ⊤).toNat + 1) t_min.val S :=
      robustQ_interlace (by omega) (near_symm hnear)
    rw [blockCore_eq_at hnb htmin_prof, blockCore_eq_at hnb ht'_prof]
    exact (barCore_eq_of_barProfile_eq hnb (hsub1.trans hsub2) (ht'_prof.trans htmin_prof.symm)).symm
  · have ht'1_le : t'.val + 1 ≤ t_max.val := by omega
    have hsub1 : robustQ C (closureSizeSup C).toNat ((nbDim C ⊤).toNat + 1) t_max.val S ⊆
        robustQ C (closureSizeSup C).toNat ((nbDim C ⊤).toNat + 1) (t'.val + 1) S :=
      robustQ_anti (by omega) S ht'1_le
    have hsub2 : robustQ C (closureSizeSup C).toNat ((nbDim C ⊤).toNat + 1) (t'.val + 1) S ⊆
        robustQ C (closureSizeSup C).toNat ((nbDim C ⊤).toNat + 1) t'.val S' :=
      robustQ_interlace (by omega) hnear
    rw [blockCore_eq_at hnb htmax_prof, blockCore_eq_at hnb ht'_prof]
    exact barCore_eq_of_barProfile_eq hnb (hsub1.trans hsub2) (htmax_prof.trans ht'_prof.symm)

lemma sum_blockLen {X : Type} {C : LanguageClass X} (hnb : nbDim C ⊤ < ⊤)
    (N : ℕ) {n : ℕ} (S : Fin n → X) :
    ∑ σ : Fin (2 ^ ((nbDim C ⊤).toNat + 1)), blockLen C hnb N S σ = N := by
  unfold blockLen blockSet
  have := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset (Fin N)))
    (t := (Finset.univ : Finset (Fin (2 ^ ((nbDim C ⊤).toNat + 1)))))
    (f := profAt C hnb N S)
    (fun t _ => Finset.mem_univ _)
  simpa using this.symm

/-- Section 5.5: Residue partition of an infinite set `K` into `b` disjoint infinite parts. -/
noncomputable def enumInfSet {X : Type} [Countable X] (K : Set X) (hK : K.Infinite) : ℕ ≃ K :=
  letI : Infinite K := hK.to_subtype
  Classical.choice (nonempty_equiv_of_countable (α := ℕ) (β := K))

noncomputable def resPart {X : Type} [Countable X] (K : Set X) (b : ℕ) (j : Fin b) : Set X :=
  if hK : K.Infinite then
    Set.range fun r : ℕ => ((enumInfSet K hK) (j.val + r * b)).val
  else
    Set.univ

lemma resPart_subset {X : Type} [Countable X] {K : Set X} (hK : K.Infinite)
    (b : ℕ) (j : Fin b) : resPart K b j ⊆ K := by
  unfold resPart
  rw [dif_pos hK]
  rintro x ⟨r, rfl⟩
  exact ((enumInfSet K hK) (j.val + r * b)).2

lemma resPart_infinite {X : Type} [Countable X] {K : Set X} (hK : K.Infinite)
    {b : ℕ} (hb : 1 ≤ b) (j : Fin b) : (resPart K b j).Infinite := by
  unfold resPart
  rw [dif_pos hK]
  refine Set.infinite_range_of_injective fun r₁ r₂ heq => ?_
  have hsub : (enumInfSet K hK) (j.val + r₁ * b) = (enumInfSet K hK) (j.val + r₂ * b) :=
    Subtype.ext heq
  have hinj := (enumInfSet K hK).injective hsub
  have hm : r₁ * b = r₂ * b := by omega
  exact Nat.eq_of_mul_eq_mul_right hb hm

lemma resPart_disjoint {X : Type} [Countable X] {K : Set X} (hK : K.Infinite)
    {b : ℕ} {j₁ j₂ : Fin b} (hne : j₁ ≠ j₂) :
    Disjoint (resPart K b j₁) (resPart K b j₂) := by
  rw [Set.disjoint_left]
  unfold resPart
  rw [dif_pos hK, dif_pos hK]
  rintro x ⟨r₁, rfl⟩ ⟨r₂, hr₂⟩
  have hsub : (enumInfSet K hK) (j₂.val + r₂ * b) = (enumInfSet K hK) (j₁.val + r₁ * b) :=
    Subtype.ext hr₂
  have hinj := (enumInfSet K hK).injective hsub
  have hmod : (j₂.val + r₂ * b) % b = (j₁.val + r₁ * b) % b := congrArg (· % b) hinj
  rw [Nat.add_mul_mod_self_right, Nat.add_mul_mod_self_right,
      Nat.mod_eq_of_lt j₂.isLt, Nat.mod_eq_of_lt j₁.isLt] at hmod
  exact hne (Fin.ext hmod.symm)

lemma card_hit_resPart_le_one {X : Type} [Countable X] {K : Set X} (hK : K.Infinite)
    {b : ℕ} (x : X) :
    (Finset.univ.filter fun j : Fin b => x ∈ resPart K b j).card ≤ 1 := by
  refine Finset.card_le_one.mpr fun j₁ hj₁ j₂ hj₂ => ?_
  by_contra hne
  exact Set.disjoint_left.mp (resPart_disjoint hK hne)
    (Finset.mem_filter.mp hj₁).2 (Finset.mem_filter.mp hj₂).2

/-- Cubic lower bound `x ^ 3 / 6 ≤ Real.exp x` for `0 ≤ x`. -/
lemma cubic_div_six_le_exp {x : ℝ} (hx : 0 ≤ x) : x ^ 3 / 6 ≤ Real.exp x := by
  have hsum := Real.sum_le_exp_of_nonneg hx 4
  have hexpand : (∑ i ∈ Finset.range 4, x ^ i / (Nat.factorial i : ℝ)) =
      1 + x + x ^ 2 / 2 + x ^ 3 / 6 := by
    simp [Finset.sum_range_succ, Nat.factorial]
  rw [hexpand] at hsum
  have hx2 : 0 ≤ x ^ 2 := sq_nonneg x
  linarith

/-- Combined Upper Bound mechanism at sample size `n` (when `N ≥ 1` and `b ≥ 1`). -/
noncomputable def upperWeight {X : Type} (C : LanguageClass X) (hnb : nbDim C ⊤ < ⊤)
    (N b : ℕ) {n : ℕ} (S : Fin n → X)
    (p : Fin (2 ^ ((nbDim C ⊤).toNat + 1)) × Fin b) : ℝ :=
  let PS := Finset.univ.filter fun σ => 0 < blockLen C hnb N S σ
  let ZS : ℝ := ∑ τ ∈ PS, Real.exp ((blockLen C hnb N S τ : ℝ) / 8)
  if p.1 ∈ PS then
    (Real.exp ((blockLen C hnb N S p.1 : ℝ) / 8) / ZS) * (1 / (b : ℝ))
  else
    0

noncomputable def upperOut {X : Type} [Countable X] (C : LanguageClass X) (hnb : nbDim C ⊤ < ⊤)
    (N b : ℕ) {n : ℕ} (S : Fin n → X)
    (p : Fin (2 ^ ((nbDim C ⊤).toNat + 1)) × Fin b) : Set X :=
  resPart (blockCore C hnb N S p.1) b p.2 \ Set.range S

lemma PS_nonempty {X : Type} {C : LanguageClass X} (hnb : nbDim C ⊤ < ⊤)
    {N n : ℕ} (hN : 1 ≤ N) (S : Fin n → X) :
    (Finset.univ.filter fun σ => 0 < blockLen C hnb N S σ).Nonempty := by
  let t₀ : Fin N := ⟨0, hN⟩
  let σ₀ := profAt C hnb N S t₀
  refine ⟨σ₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
  exact Finset.card_pos.mpr ⟨t₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩

lemma upperWeight_nonneg {X : Type} {C : LanguageClass X} (hnb : nbDim C ⊤ < ⊤)
    {N b n : ℕ} (S : Fin n → X) (p : Fin (2 ^ ((nbDim C ⊤).toNat + 1)) × Fin b) :
    0 ≤ upperWeight C hnb N b S p := by
  unfold upperWeight
  dsimp only
  split_ifs with hp
  · refine mul_nonneg (div_nonneg (Real.exp_pos _).le ?_) (by positivity)
    exact Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le
  · exact le_refl 0

lemma upperWeight_sum_one {X : Type} {C : LanguageClass X} (hnb : nbDim C ⊤ < ⊤)
    {N b n : ℕ} (hN : 1 ≤ N) (hb : 1 ≤ b) (S : Fin n → X) :
    ∑ p : Fin (2 ^ ((nbDim C ⊤).toNat + 1)) × Fin b, upperWeight C hnb N b S p = 1 := by
  unfold upperWeight
  dsimp only
  set PS := Finset.univ.filter fun σ => 0 < blockLen C hnb N S σ
  set ZS : ℝ := ∑ τ ∈ PS, Real.exp ((blockLen C hnb N S τ : ℝ) / 8)
  have hPS_ne : PS.Nonempty := PS_nonempty hnb hN S
  have hZS_pos : 0 < ZS := Finset.sum_pos (fun _ _ => Real.exp_pos _) hPS_ne
  have hb_ne : (b : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [Fintype.sum_prod_type]
  have hinner : ∀ σ : Fin (2 ^ ((nbDim C ⊤).toNat + 1)),
      (∑ _j : Fin b, if σ ∈ PS then Real.exp ((blockLen C hnb N S σ : ℝ) / 8) / ZS * (1 / (b : ℝ)) else 0) =
        if σ ∈ PS then Real.exp ((blockLen C hnb N S σ : ℝ) / 8) / ZS else 0 := by
    intro σ
    split_ifs with hσ
    · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp [hb_ne]
    · simp
  simp_rw [hinner]
  rw [← Finset.sum_filter]
  have hfilter : Finset.univ.filter (· ∈ PS) = PS := by
    ext σ; simp
  rw [hfilter, ← Finset.sum_div, div_self hZS_pos.ne']

/-- Theorem 5.16 + 5.17 combined: Upper bound direction of Theorem 1.1! -/
theorem upper_bound {X : Type} [Countable X] (C : LanguageClass X)
    (hcdim : closureDim C < ⊤) (hnb : nbDim C ⊤ < ⊤) :
    PrivatelyUniformlyGeneratable C := by
  have hc : closureSizeSup C < ⊤ := (closureDim_lt_top_iff C).mp hcdim
  let c : ℕ := (closureSizeSup C).toNat
  let d : ℕ := (nbDim C ⊤).toNat
  let h : ℕ := d + 1
  let M : ℕ := 2 ^ (d + 1)
  have hM_pos : 1 ≤ M := Nat.one_le_pow (d + 1) 2 (by omega)
  have hh_ge1 : 1 ≤ h := by omega
  let K₀ : ℕ := max 2 (Nat.ceil (2 * (M : ℝ) * Real.exp (1 / 4)))
  let A_const : ℕ := 16 * h * M
  let n₀ : ℕ := max (max 2 (2 * (c + h))) (6 * K₀ * A_const ^ 3)
  have hn₀_ge1 : 1 ≤ n₀ := by omega
  let δ : ℕ → ℝ := fun n => if n = 0 then 1 else 1 / ((n : ℝ) ^ 2)
  have htend : Tendsto (fun n : ℕ => (n : ℝ) * δ n) atTop (nhds 0) := by
    have hcongr : (fun n : ℕ => (n : ℝ) * δ n) =ᶠ[atTop] fun n : ℕ => 1 / (n : ℝ) := by
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hn0 : n ≠ 0 := by omega
      have hnr : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn0
      simp only [δ, if_neg hn0]
      field_simp [hnr]
    exact tendsto_one_div_atTop_nhds_zero_nat.congr' hcongr.symm
  -- Define mechanism `mech n` for all `n : ℕ`.
  let N_of : ℕ → ℕ := fun n => max 1 ((n - c) / h)
  let b_of : ℕ → ℕ := fun n => 4 * n ^ 2 + 1
  let mech : ∀ n : ℕ, Mechanism X (Set X) n := fun n S =>
    finitePM
      (upperWeight C hnb (N_of n) (b_of n) S)
      (upperWeight_nonneg hnb S)
      (upperWeight_sum_one hnb (le_max_left 1 _) (by dsimp [b_of]; omega) S)
      (upperOut C hnb (N_of n) (b_of n) S)
  refine ⟨n₀, hn₀_ge1, δ, mech, htend, fun n hn => ⟨?_, ?_⟩⟩
  · -- Privacy: `IsDP (mech n) 1 (δ n)` for `n ≥ n₀`!
    have hn_ge2 : 2 ≤ n := le_trans (le_trans (le_max_left 2 _) (le_max_left _ _)) hn
    have hn_2ch : 2 * (c + h) ≤ n := le_trans (le_trans (le_max_right 2 _) (le_max_left _ _)) hn
    have hn_cub : 6 * K₀ * A_const ^ 3 ≤ n := le_trans (le_max_right _ _) hn
    have hn0 : n ≠ 0 := by omega
    have hδn : δ n = 1 / ((n : ℝ) ^ 2) := if_neg hn0
    set N := N_of n
    set b := b_of n
    have hdiv_pos : 1 ≤ (n - c) / h := Nat.div_pos (by omega) (by omega)
    have hN_eq : N = (n - c) / h := max_eq_right hdiv_pos
    have hN_ge1 : 1 ≤ N := by omega
    have hb_ge1 : 1 ≤ b := by dsimp [b, b_of]; omega
    -- Bound `N ≥ n / (2 * h)` in `ℝ`, hence `ZS ≥ 2 * M * exp(1/4) * n^2`.
    have hN_real_lb : (n : ℝ) / (2 * (h : ℝ)) ≤ (N : ℝ) := by
      have hmod : (n - c) % h < h := Nat.mod_lt (n - c) (by omega)
      have hdiv_mod : h * N + (n - c) % h = n - c := by
        rw [hN_eq]; exact Nat.div_add_mod (n - c) h
      have hnat : n ≤ c + h * N + h := by omega
      have hreal : (n : ℝ) ≤ (c : ℝ) + (h : ℝ) * (N : ℝ) + (h : ℝ) := by exact_mod_cast hnat
      have h2ch_r : 2 * ((c : ℝ) + (h : ℝ)) ≤ (n : ℝ) := by exact_mod_cast hn_2ch
      have hh_pos : (0 : ℝ) < (h : ℝ) := by positivity
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    have hZS_lb_all : ∀ S_any : Fin n → X,
        2 * (M : ℝ) * Real.exp (1 / 4) * ((n : ℝ) ^ 2) ≤
          ∑ τ ∈ Finset.univ.filter (fun σ => 0 < blockLen C hnb N S_any σ),
            Real.exp ((blockLen C hnb N S_any τ : ℝ) / 8) := by
      intro S_any
      -- Pigeonhole: some `σ₀` has `M * blockLen σ₀ ≥ N`.
      have hpigeon : ∃ σ₀ : Fin M, N ≤ M * blockLen C hnb N S_any σ₀ := by
        by_contra hall
        have hsum_lt : ∑ σ : Fin M, (M * blockLen C hnb N S_any σ) < ∑ _σ : Fin M, N := by
          refine Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty_iff.mpr ⟨⟨0, hM_pos⟩⟩) fun σ _ => ?_
          exact Nat.lt_of_not_ge fun hle => hall ⟨σ, hle⟩
        rw [← Finset.mul_sum, sum_blockLen hnb N S_any, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, smul_eq_mul] at hsum_lt
        exact Nat.lt_irrefl (M * N) hsum_lt
      obtain ⟨σ₀, hσ₀_ge⟩ := hpigeon
      have hσ₀_pos : 0 < blockLen C hnb N S_any σ₀ := by
        by_contra h0
        have : blockLen C hnb N S_any σ₀ = 0 := by omega
        rw [this, mul_zero] at hσ₀_ge
        omega
      have hσ₀_mem : σ₀ ∈ Finset.univ.filter (fun σ => 0 < blockLen C hnb N S_any σ) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hσ₀_pos⟩
      have hsingle : Real.exp ((blockLen C hnb N S_any σ₀ : ℝ) / 8) ≤
          ∑ τ ∈ Finset.univ.filter (fun σ => 0 < blockLen C hnb N S_any σ),
            Real.exp ((blockLen C hnb N S_any τ : ℝ) / 8) :=
        Finset.single_le_sum (f := fun τ => Real.exp ((blockLen C hnb N S_any τ : ℝ) / 8))
          (fun _ _ => (Real.exp_pos _).le) hσ₀_mem
      have hx_ge : (n : ℝ) / (A_const : ℝ) ≤ (blockLen C hnb N S_any σ₀ : ℝ) / 8 := by
        have h1 : (N : ℝ) ≤ (M : ℝ) * (blockLen C hnb N S_any σ₀ : ℝ) := by exact_mod_cast hσ₀_ge
        have hA : (A_const : ℝ) = 16 * (h : ℝ) * (M : ℝ) := by exact_mod_cast rfl
        have hM_r : (0 : ℝ) < (M : ℝ) := by positivity
        have hh_r : (0 : ℝ) < (h : ℝ) := by positivity
        rw [hA, div_le_div_iff₀ (by positivity) (by positivity)]
        have h2 : (n : ℝ) ≤ (N : ℝ) * (2 * (h : ℝ)) :=
          (div_le_iff₀ (by positivity)).mp hN_real_lb
        nlinarith
      have hx_nonneg : 0 ≤ (n : ℝ) / (A_const : ℝ) := by positivity
      have hexp_mono : Real.exp ((n : ℝ) / (A_const : ℝ)) ≤
          Real.exp ((blockLen C hnb N S_any σ₀ : ℝ) / 8) :=
        Real.exp_le_exp.mpr hx_ge
      have hcub : ((n : ℝ) / (A_const : ℝ)) ^ 3 / 6 ≤ Real.exp ((n : ℝ) / (A_const : ℝ)) :=
        cubic_div_six_le_exp hx_nonneg
      have hK₀_ge : 2 * (M : ℝ) * Real.exp (1 / 4) ≤ (K₀ : ℝ) := by
        have hceil := Nat.le_ceil (2 * (M : ℝ) * Real.exp (1 / 4))
        have hmax : Nat.ceil (2 * (M : ℝ) * Real.exp (1 / 4)) ≤ K₀ := le_max_right 2 _
        exact hceil.trans (by exact_mod_cast hmax)
      have hn_cub_r : 6 * (K₀ : ℝ) * ((A_const : ℝ) ^ 3) ≤ (n : ℝ) := by exact_mod_cast hn_cub
      have hA_pos : (0 : ℝ) < (A_const : ℝ) := by
        have : 0 < A_const := by dsimp [A_const]; positivity
        exact_mod_cast this
      have hpoly : 2 * (M : ℝ) * Real.exp (1 / 4) * ((n : ℝ) ^ 2) ≤
          ((n : ℝ) / (A_const : ℝ)) ^ 3 / 6 := by
        rw [div_pow, div_div, le_div_iff₀ (by positivity)]
        have hmul_n2 : 2 * (M : ℝ) * Real.exp (1 / 4) * ((n : ℝ) ^ 2) * ((A_const : ℝ) ^ 3 * 6) ≤
            (K₀ : ℝ) * ((n : ℝ) ^ 2) * ((A_const : ℝ) ^ 3 * 6) := by
          gcongr
        have hn_pos : (0 : ℝ) ≤ (n : ℝ) ^ 2 := sq_nonneg _
        calc 2 * (M : ℝ) * Real.exp (1 / 4) * ((n : ℝ) ^ 2) * ((A_const : ℝ) ^ 3 * 6)
            ≤ (K₀ : ℝ) * ((n : ℝ) ^ 2) * ((A_const : ℝ) ^ 3 * 6) := hmul_n2
          _ = (6 * (K₀ : ℝ) * ((A_const : ℝ) ^ 3)) * ((n : ℝ) ^ 2) := by ring
          _ ≤ (n : ℝ) * ((n : ℝ) ^ 2) := mul_le_mul_of_nonneg_right hn_cub_r hn_pos
          _ = (n : ℝ) ^ 3 := by ring
      linarith
    -- Now verify the DP inequality on `Neighbors S S'` and measurable `O : Set (Set X)`!
    intro S S' hnb_SS' O hO
    have hnear : Near S S' := Or.inr hnb_SS'
    obtain ⟨i₀, _, hrest_SS'⟩ := hnb_SS'
    dsimp only [mech]
    rw [finitePM_real_apply _ _ _ _ hO, finitePM_real_apply _ _ _ _ hO]
    set PS := Finset.univ.filter fun σ => 0 < blockLen C hnb N S σ
    set PS' := Finset.univ.filter fun σ => 0 < blockLen C hnb N S' σ
    set ZS : ℝ := ∑ τ ∈ PS, Real.exp ((blockLen C hnb N S τ : ℝ) / 8)
    set ZS' : ℝ := ∑ τ ∈ PS', Real.exp ((blockLen C hnb N S' τ : ℝ) / 8)
    have hZS_big : 2 * (M : ℝ) * Real.exp (1 / 4) * ((n : ℝ) ^ 2) ≤ ZS := hZS_lb_all S
    have hZS_pos : 0 < ZS := by
      have : (0 : ℝ) < 2 * (M : ℝ) * Real.exp (1 / 4) * ((n : ℝ) ^ 2) := by positivity
      linarith
    have hZS'_pos : 0 < ZS' :=
      Finset.sum_pos (fun _ _ => Real.exp_pos _) (PS_nonempty hnb hN_ge1 S')
    -- Bound `ZS' ≤ exp(3/4) * ZS`.
    have hZS_ge_2M : 2 * (M : ℝ) ≤ ZS := by
      have hexp_ge1 : (1 : ℝ) ≤ Real.exp (1 / 4) := Real.one_le_exp (by norm_num)
      have hn2_ge1 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by
        have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_ge2
        nlinarith
      have h1 : 2 * (M : ℝ) * 1 * 1 ≤ 2 * (M : ℝ) * Real.exp (1 / 4) * ((n : ℝ) ^ 2) := by
        gcongr
      linarith
    have hZS'_le : ZS' ≤ Real.exp (3 / 4) * ZS := by
      have hterm_le : ∀ τ ∈ PS',
          Real.exp ((blockLen C hnb N S' τ : ℝ) / 8) ≤
            if τ ∈ PS then Real.exp (1 / 4) * Real.exp ((blockLen C hnb N S τ : ℝ) / 8)
            else Real.exp (1 / 4) := by
        intro τ _
        have hdiff := blockLen_near_le hc hnb hN_ge1 (near_symm hnear) τ
        split_ifs with hτPS
        · rw [← Real.exp_add]
          apply Real.exp_le_exp.mpr
          have hcast : (blockLen C hnb N S' τ : ℝ) ≤ (blockLen C hnb N S τ : ℝ) + 2 := by
            exact_mod_cast hdiff
          linarith
        · have h0 : blockLen C hnb N S τ = 0 := by
            simp only [PS, Finset.mem_filter, Finset.mem_univ, true_and, not_lt,
              Nat.le_zero] at hτPS
            exact hτPS
          rw [h0] at hdiff
          apply Real.exp_le_exp.mpr
          have hcast : (blockLen C hnb N S' τ : ℝ) ≤ 2 := by exact_mod_cast hdiff
          linarith
      have hsum1 : ZS' ≤ ∑ τ : Fin M,
          (if τ ∈ PS then Real.exp (1 / 4) * Real.exp ((blockLen C hnb N S τ : ℝ) / 8)
           else Real.exp (1 / 4)) := by
        calc ZS'
            ≤ ∑ τ ∈ PS',
                (if τ ∈ PS then Real.exp (1 / 4) * Real.exp ((blockLen C hnb N S τ : ℝ) / 8)
                 else Real.exp (1 / 4)) := Finset.sum_le_sum hterm_le
          _ ≤ ∑ τ : Fin M, _ := by
              refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun τ _ _ => ?_
              split_ifs <;> positivity
      have hsum2 : (∑ τ : Fin M,
          (if τ ∈ PS then Real.exp (1 / 4) * Real.exp ((blockLen C hnb N S τ : ℝ) / 8)
           else Real.exp (1 / 4))) ≤ Real.exp (1 / 4) * (ZS + (M : ℝ)) := by
        have hle_each : ∀ τ : Fin M,
            (if τ ∈ PS then Real.exp (1 / 4) * Real.exp ((blockLen C hnb N S τ : ℝ) / 8)
             else Real.exp (1 / 4)) ≤
            (if τ ∈ PS then Real.exp (1 / 4) * Real.exp ((blockLen C hnb N S τ : ℝ) / 8) else 0) +
              Real.exp (1 / 4) := by
          intro τ; split_ifs <;> linarith [Real.exp_pos (1 / 4)]
        calc _
            ≤ ∑ τ : Fin M,
                ((if τ ∈ PS then Real.exp (1 / 4) * Real.exp ((blockLen C hnb N S τ : ℝ) / 8) else 0) +
                  Real.exp (1 / 4)) := Finset.sum_le_sum fun τ _ => hle_each τ
          _ = Real.exp (1 / 4) * ZS + (M : ℝ) * Real.exp (1 / 4) := by
              rw [Finset.sum_add_distrib, ← Finset.sum_filter]
              have hf : Finset.univ.filter (· ∈ PS) = PS := by ext x; simp
              rw [hf, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
                nsmul_eq_mul]
          _ = Real.exp (1 / 4) * (ZS + (M : ℝ)) := by ring
      have h15_le : ZS + (M : ℝ) ≤ Real.exp (1 / 2) * ZS := by
        have h12 : (1 : ℝ) + 1 / 2 ≤ Real.exp (1 / 2) := by
          have := Real.add_one_le_exp (1 / 2 : ℝ)
          linarith
        have hM_half : (M : ℝ) ≤ (1 / 2) * ZS := by linarith
        nlinarith
      calc ZS'
          ≤ Real.exp (1 / 4) * (ZS + (M : ℝ)) := hsum1.trans hsum2
        _ ≤ Real.exp (1 / 4) * (Real.exp (1 / 2) * ZS) := by
            gcongr
        _ = Real.exp (3 / 4) * ZS := by
            rw [← mul_assoc, ← Real.exp_add]
            norm_num
    -- Split `σ : Fin M` into `G = {σ ∈ PS | 3 ≤ blockLen σ}` and complement!
    let G := PS.filter fun σ => 3 ≤ blockLen C hnb N S σ
    -- For each `σ ∈ G`, define `Bad σ = {j : Fin b | S i₀ ∈ resPart K b j ∨ S' i₀ ∈ resPart K b j}`.
    let Bad : Fin M → Finset (Fin b) := fun σ =>
      Finset.univ.filter fun j : Fin b =>
        S i₀ ∈ resPart (blockCore C hnb N S σ) b j ∨
        S' i₀ ∈ resPart (blockCore C hnb N S σ) b j
    have hBad_card : ∀ σ : Fin M, (Bad σ).card ≤ 2 := by
      intro σ
      have hK_inf : (blockCore C hnb N S σ).Infinite := by
        unfold blockCore
        split_ifs with hne_b
        · exact barCore_infinite hnb _
        · have : Infinite X := infinite_X_of_languageClass C
          exact Set.infinite_univ
      have hsub : Bad σ ⊆
          (Finset.univ.filter fun j : Fin b => S i₀ ∈ resPart (blockCore C hnb N S σ) b j) ∪
          (Finset.univ.filter fun j : Fin b => S' i₀ ∈ resPart (blockCore C hnb N S σ) b j) := by
        intro j hj
        simp only [Bad, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hj ⊢
        exact hj
      have hc1 := Finset.card_le_card hsub
      have hc2 := Finset.card_union_le
        (Finset.univ.filter fun j : Fin b => S i₀ ∈ resPart (blockCore C hnb N S σ) b j)
        (Finset.univ.filter fun j : Fin b => S' i₀ ∈ resPart (blockCore C hnb N S σ) b j)
      have hc3 := card_hit_resPart_le_one hK_inf (b := b) (S i₀)
      have hc4 := card_hit_resPart_le_one hK_inf (b := b) (S' i₀)
      omega
    -- On `σ ∈ G` and `j ∉ Bad σ`, `upperOut S (σ, j) = upperOut S' (σ, j)` AND weight ratio `≤ exp 1`!
    have hgood_out : ∀ σ ∈ G, ∀ j : Fin b, j ∉ Bad σ →
        upperOut C hnb N b S (σ, j) = upperOut C hnb N b S' (σ, j) := by
      intro σ hσG j hjBad
      have hlen3 : 3 ≤ blockLen C hnb N S σ := (Finset.mem_filter.mp hσG).2
      obtain ⟨_, hcore_eq⟩ := blockCore_eq_of_ge_three hc hnb hN_ge1 hnear hlen3
      simp only [Bad, Finset.mem_filter, Finset.mem_univ, true_and, not_or] at hjBad
      unfold upperOut
      dsimp only
      rw [← hcore_eq]
      ext x
      simp only [Set.mem_sdiff, Set.mem_range]
      refine and_congr_right fun hx_res => ?_
      refine not_congr ⟨?_, ?_⟩
      · rintro ⟨k, rfl⟩
        by_cases hk : k = i₀
        · subst hk; exact absurd hx_res hjBad.1
        · exact ⟨k, (hrest_SS' k hk).symm⟩
      · rintro ⟨k, rfl⟩
        by_cases hk : k = i₀
        · subst hk; exact absurd hx_res hjBad.2
        · exact ⟨k, hrest_SS' k hk⟩
    have hw_S_eq : ∀ σ j, upperWeight C hnb N b S (σ, j) =
        if σ ∈ PS then (Real.exp ((blockLen C hnb N S σ : ℝ) / 8) / ZS) * (1 / (b : ℝ)) else 0 :=
      fun _ _ => rfl
    have hw_S'_eq : ∀ σ j, upperWeight C hnb N b S' (σ, j) =
        if σ ∈ PS' then (Real.exp ((blockLen C hnb N S' σ : ℝ) / 8) / ZS') * (1 / (b : ℝ)) else 0 :=
      fun _ _ => rfl
    have hgood_wt : ∀ σ ∈ G, ∀ j : Fin b,
        upperWeight C hnb N b S (σ, j) ≤ Real.exp 1 * upperWeight C hnb N b S' (σ, j) := by
      intro σ hσG j
      obtain ⟨hσPS, hlen3⟩ := Finset.mem_filter.mp hσG
      obtain ⟨hlen1', _⟩ := blockCore_eq_of_ge_three hc hnb hN_ge1 hnear hlen3
      have hσPS' : σ ∈ PS' := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
      rw [hw_S_eq, hw_S'_eq, if_pos hσPS, if_pos hσPS']
      have hdiff := blockLen_near_le hc hnb hN_ge1 hnear σ
      have hexp_diff : Real.exp ((blockLen C hnb N S σ : ℝ) / 8) ≤
          Real.exp (1 / 4) * Real.exp ((blockLen C hnb N S' σ : ℝ) / 8) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have hcast : (blockLen C hnb N S σ : ℝ) ≤ (blockLen C hnb N S' σ : ℝ) + 2 := by
          exact_mod_cast hdiff
        linarith
      have hratio : Real.exp ((blockLen C hnb N S σ : ℝ) / 8) / ZS ≤
          Real.exp 1 * (Real.exp ((blockLen C hnb N S' σ : ℝ) / 8) / ZS') := by
        rw [div_le_iff₀ hZS_pos, mul_div_assoc', div_mul_eq_mul_div, le_div_iff₀ hZS'_pos]
        calc Real.exp ((blockLen C hnb N S σ : ℝ) / 8) * ZS'
            ≤ (Real.exp (1 / 4) * Real.exp ((blockLen C hnb N S' σ : ℝ) / 8)) *
                (Real.exp (3 / 4) * ZS) :=
              mul_le_mul hexp_diff hZS'_le hZS'_pos.le
                (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
          _ = Real.exp 1 * Real.exp ((blockLen C hnb N S' σ : ℝ) / 8) * ZS := by
              have hexp1 : Real.exp (1 / 4) * Real.exp (3 / 4) = Real.exp 1 := by
                rw [← Real.exp_add]; norm_num
              calc (Real.exp (1 / 4) * Real.exp ((blockLen C hnb N S' σ : ℝ) / 8)) *
                      (Real.exp (3 / 4) * ZS)
                  = (Real.exp (1 / 4) * Real.exp (3 / 4)) *
                      Real.exp ((blockLen C hnb N S' σ : ℝ) / 8) * ZS := by ring
                _ = Real.exp 1 * Real.exp ((blockLen C hnb N S' σ : ℝ) / 8) * ZS := by rw [hexp1]
      have hb_inv : 0 ≤ (1 : ℝ) / (b : ℝ) := by positivity
      calc (Real.exp ((blockLen C hnb N S σ : ℝ) / 8) / ZS) * (1 / (b : ℝ))
          ≤ (Real.exp 1 * (Real.exp ((blockLen C hnb N S' σ : ℝ) / 8) / ZS')) * (1 / (b : ℝ)) :=
            mul_le_mul_of_nonneg_right hratio hb_inv
        _ = Real.exp 1 * ((Real.exp ((blockLen C hnb N S' σ : ℝ) / 8) / ZS') * (1 / (b : ℝ))) := by
            ring
    -- Pointwise bound on each `(σ, j) : Fin M × Fin b`!
    have hptwise : ∀ p : Fin M × Fin b,
        (if upperOut C hnb N b S p ∈ O then upperWeight C hnb N b S p else 0) ≤
          Real.exp 1 * (if upperOut C hnb N b S' p ∈ O then upperWeight C hnb N b S' p else 0) +
          (if p.1 ∉ G then upperWeight C hnb N b S p else 0) +
          (if p.1 ∈ G ∧ p.2 ∈ Bad p.1 then upperWeight C hnb N b S p else 0) := by
      rintro ⟨σ, j⟩
      dsimp only
      have hw0 := upperWeight_nonneg hnb (N := N) S (σ, j)
      have hw0' : 0 ≤ Real.exp 1 *
          (if upperOut C hnb N b S' (σ, j) ∈ O then upperWeight C hnb N b S' (σ, j) else 0) := by
        by_cases hmem' : upperOut C hnb N b S' (σ, j) ∈ O
        · rw [if_pos hmem']
          exact mul_nonneg (Real.exp_pos 1).le (upperWeight_nonneg hnb (N := N) S' (σ, j))
        · rw [if_neg hmem']; simp
      by_cases hσG : σ ∈ G
      · by_cases hjBad : j ∈ Bad σ
        · simp only [hσG, not_true_eq_false, ↓reduceIte, hjBad, and_self]
          by_cases hmemO : upperOut C hnb N b S (σ, j) ∈ O <;> simp only [hmemO, ↓reduceIte] <;> linarith
        · simp only [hσG, not_true_eq_false, ↓reduceIte, hjBad, and_false]
          rw [hgood_out σ hσG j hjBad]
          by_cases hmemO : upperOut C hnb N b S' (σ, j) ∈ O <;> simp only [hmemO, ↓reduceIte]
          · linarith [hgood_wt σ hσG j]
          · linarith
      · simp only [hσG, not_false_eq_true, ↓reduceIte, false_and]
        by_cases hmemO : upperOut C hnb N b S (σ, j) ∈ O <;> simp only [hmemO, ↓reduceIte] <;> linarith
    -- Bound the first error sum `∑ p, (if p.1 ∉ G then upperWeight S p else 0) ≤ δ n / 2`!
    have herr1 : (∑ p : Fin M × Fin b,
        if p.1 ∉ G then upperWeight C hnb N b S p else 0) ≤ δ n / 2 := by
      rw [Fintype.sum_prod_type]
      have hb_ne : (b : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hrow : ∀ σ : Fin M,
          (∑ j : Fin b, if σ ∉ G then upperWeight C hnb N b S (σ, j) else 0) ≤
            Real.exp (1 / 4) / ZS := by
        intro σ
        by_cases hσG : σ ∈ G
        · simp only [hσG, not_true_eq_false, ↓reduceIte, Finset.sum_const_zero]
          exact div_nonneg (Real.exp_pos _).le hZS_pos.le
        · simp only [hσG, not_false_eq_true, ↓reduceIte]
          simp_rw [hw_S_eq σ]
          by_cases hσPS : σ ∈ PS
          · simp only [if_pos hσPS, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
              nsmul_eq_mul]
            have hsimp : (b : ℝ) * ((Real.exp ((blockLen C hnb N S σ : ℝ) / 8) / ZS) * (1 / (b : ℝ))) =
                Real.exp ((blockLen C hnb N S σ : ℝ) / 8) / ZS := by field_simp [hb_ne]
            rw [hsimp]
            have hle2 : blockLen C hnb N S σ ≤ 2 := by
              have hnot3 : ¬ (3 ≤ blockLen C hnb N S σ) := fun h3 =>
                hσG (Finset.mem_filter.mpr ⟨hσPS, h3⟩)
              omega
            apply div_le_div_of_nonneg_right _ hZS_pos.le
            apply Real.exp_le_exp.mpr
            have hcast : (blockLen C hnb N S σ : ℝ) ≤ 2 := by exact_mod_cast hle2
            linarith
          · simp only [if_neg hσPS, Finset.sum_const_zero]
            exact div_nonneg (Real.exp_pos _).le hZS_pos.le
      calc (∑ σ : Fin M, ∑ j : Fin b, if σ ∉ G then upperWeight C hnb N b S (σ, j) else 0)
          ≤ ∑ _σ : Fin M, Real.exp (1 / 4) / ZS := Finset.sum_le_sum fun σ _ => hrow σ
        _ = (M : ℝ) * Real.exp (1 / 4) / ZS := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_div_assoc]
        _ ≤ δ n / 2 := by
            rw [hδn, div_div, div_le_div_iff₀ hZS_pos (by positivity)]
            linarith
    -- Bound the second error sum `∑ p, (if p.1 ∈ G ∧ p.2 ∈ Bad p.1 then upperWeight S p else 0) ≤ δ n / 2`!
    have herr2 : (∑ p : Fin M × Fin b,
        if p.1 ∈ G ∧ p.2 ∈ Bad p.1 then upperWeight C hnb N b S p else 0) ≤ δ n / 2 := by
      rw [Fintype.sum_prod_type]
      have hrow2 : ∀ σ : Fin M,
          (∑ j : Fin b, if σ ∈ G ∧ j ∈ Bad σ then upperWeight C hnb N b S (σ, j) else 0) ≤
            (if σ ∈ PS then Real.exp ((blockLen C hnb N S σ : ℝ) / 8) / ZS else 0) * (2 / (b : ℝ)) := by
        intro σ
        by_cases hσG : σ ∈ G
        · have hσPS : σ ∈ PS := (Finset.mem_filter.mp hσG).1
          simp only [hσG, true_and, hσPS, ↓reduceIte]
          simp_rw [hw_S_eq σ, if_pos hσPS]
          rw [← Finset.sum_filter]
          have hf : Finset.univ.filter (· ∈ Bad σ) = Bad σ := by ext x; simp
          rw [hf, Finset.sum_const, nsmul_eq_mul]
          have hbc : ((Bad σ).card : ℝ) ≤ 2 := by exact_mod_cast hBad_card σ
          have hnonneg : 0 ≤ (Real.exp ((blockLen C hnb N S σ : ℝ) / 8) / ZS) * (1 / (b : ℝ)) :=
            mul_nonneg (div_nonneg (Real.exp_pos _).le hZS_pos.le) (by positivity)
          calc ((Bad σ).card : ℝ) * ((Real.exp ((blockLen C hnb N S σ : ℝ) / 8) / ZS) * (1 / (b : ℝ)))
              ≤ 2 * ((Real.exp ((blockLen C hnb N S σ : ℝ) / 8) / ZS) * (1 / (b : ℝ))) :=
                mul_le_mul_of_nonneg_right hbc hnonneg
            _ = (Real.exp ((blockLen C hnb N S σ : ℝ) / 8) / ZS) * (2 / (b : ℝ)) := by ring
        · simp only [hσG, false_and, ↓reduceIte, Finset.sum_const_zero]
          split_ifs
          · exact mul_nonneg (div_nonneg (Real.exp_pos _).le hZS_pos.le) (by positivity)
          · simp
      calc (∑ σ : Fin M, ∑ j : Fin b,
              if σ ∈ G ∧ j ∈ Bad σ then upperWeight C hnb N b S (σ, j) else 0)
          ≤ ∑ σ : Fin M,
              (if σ ∈ PS then Real.exp ((blockLen C hnb N S σ : ℝ) / 8) / ZS else 0) * (2 / (b : ℝ)) :=
            Finset.sum_le_sum fun σ _ => hrow2 σ
        _ = (∑ σ : Fin M, if σ ∈ PS then Real.exp ((blockLen C hnb N S σ : ℝ) / 8) / ZS else 0) *
              (2 / (b : ℝ)) := (Finset.sum_mul _ _ _).symm
        _ = 1 * (2 / (b : ℝ)) := by
            congr 1
            rw [← Finset.sum_filter]
            have hf : Finset.univ.filter (· ∈ PS) = PS := by ext x; simp
            rw [hf, ← Finset.sum_div, div_self hZS_pos.ne']
        _ = 2 / (b : ℝ) := one_mul _
        _ ≤ δ n / 2 := by
            rw [hδn]
            have hb_r : (b : ℝ) = 4 * ((n : ℝ) ^ 2) + 1 := by
              dsimp [b, b_of]; push_cast; ring
            rw [hb_r, div_le_div_iff₀ (by positivity) (by positivity)]
            have : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
            rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
            linarith
    -- Sum `hptwise` over `p : Fin M × Fin b`!
    calc (∑ p : Fin M × Fin b,
            if upperOut C hnb N b S p ∈ O then upperWeight C hnb N b S p else 0)
        ≤ ∑ p : Fin M × Fin b,
            (Real.exp 1 * (if upperOut C hnb N b S' p ∈ O then upperWeight C hnb N b S' p else 0) +
              (if p.1 ∉ G then upperWeight C hnb N b S p else 0) +
              (if p.1 ∈ G ∧ p.2 ∈ Bad p.1 then upperWeight C hnb N b S p else 0)) :=
          Finset.sum_le_sum fun p _ => hptwise p
      _ = Real.exp 1 * (∑ p : Fin M × Fin b,
            if upperOut C hnb N b S' p ∈ O then upperWeight C hnb N b S' p else 0) +
          (∑ p : Fin M × Fin b, if p.1 ∉ G then upperWeight C hnb N b S p else 0) +
          (∑ p : Fin M × Fin b,
            if p.1 ∈ G ∧ p.2 ∈ Bad p.1 then upperWeight C hnb N b S p else 0) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
      _ ≤ Real.exp 1 * (∑ p : Fin M × Fin b,
            if upperOut C hnb N b S' p ∈ O then upperWeight C hnb N b S' p else 0) + δ n := by
          linarith
  · -- Utility: `IsUniformGenerator C (mech n)` for `n ≥ n₀`!
    intro L hL S hSL hinj
    have hn_2ch : 2 * (c + h) ≤ n := le_trans (le_trans (le_max_right 2 _) (le_max_left _ _)) hn
    set N := N_of n
    set b := b_of n
    have hdiv_pos : 1 ≤ (n - c) / h := Nat.div_pos (by omega) (by omega)
    have hN_eq : N = (n - c) / h := max_eq_right hdiv_pos
    have hb_ge1 : 1 ≤ b := by dsimp [b, b_of]; omega
    have hcard_S : (support S).card = n := by
      unfold support
      rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
    have hmeas_good : MeasurableSet {Z : Set X | Z.Infinite ∧ Z ⊆ L \ Set.range S} :=
      measurableSet_infinite.inter (measurableSet_subset (L \ Set.range S))
    dsimp only [mech]
    refine finitePM_ae _ _ _ _ hmeas_good ?_
    rintro ⟨σ, j⟩ hw_ne
    -- Since `upperWeight ≠ 0`, `σ ∈ PS`, so `0 < blockLen σ`!
    have hσ_pos : 0 < blockLen C hnb N S σ := by
      unfold upperWeight at hw_ne
      dsimp only at hw_ne
      split_ifs at hw_ne with hσPS
      · exact (Finset.mem_filter.mp hσPS).2
      · exact absurd rfl hw_ne
    obtain ⟨t, ht_mem⟩ := Finset.card_pos.mp hσ_pos
    have ht_prof : profAt C hnb N S t = σ := (Finset.mem_filter.mp ht_mem).2
    -- Show `c + h * t.val < (support S).card` and `(RSet C t.val S).Nonempty`!
    have ht_lt : t.val < (n - c) / h := hN_eq ▸ t.isLt
    have hmul_le : h * (t.val + 1) ≤ n - c := by
      have := Nat.mul_le_mul_left h (Nat.succ_le_of_lt ht_lt)
      exact this.trans (Nat.mul_div_le (n - c) h)
    have hcard_gt : c + h * t.val < (support S).card := by
      have : h * (t.val + 1) = h * t.val + h := Nat.mul_succ h t.val
      omega
    have ht_le_S : t.val ≤ (support S).card := by
      have : t.val ≤ h * t.val := Nat.le_mul_of_pos_left t.val hh_ge1
      omega
    have hS_sub_L : (↑(support S) : Set X) ⊆ L := by
      intro x hx
      unfold support at hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      exact hSL i
    have hR_ne : (RSet C t.val S).Nonempty := by
      obtain ⟨T, hTS, hTcard⟩ := Finset.exists_subset_card_eq (s := support S)
        (n := (support S).card - t.val) (by omega)
      exact ⟨T, hTS, by omega, ⟨L, hL, (Finset.coe_subset.mpr hTS).trans hS_sub_L⟩⟩
    have hQ_ic : robustQ C c h t.val S ∈ infiniteClosure C :=
      robustQ_mem_infiniteClosure hc hnb hcard_gt hR_ne
    -- Also `robustQ C c h 0 S ⊆ L` because `support S ∈ RSet C 0 S`!
    have hS_in_R0 : support S ∈ RSet C 0 S :=
      ⟨Finset.Subset.refl _, by omega, ⟨L, hL, hS_sub_L⟩⟩
    have hQ0_sub_L : robustQ C c h 0 S ⊆ L := by
      unfold robustQ
      have hnot0 : ¬ ((support S).card ≤ c + h * 0) := by omega
      rw [if_neg hnot0, if_pos ⟨support S, hS_in_R0⟩]
      have hmem_im : closure C (↑(support S) : Set X) ∈
          (fun T : Finset X => closure C (↑T : Set X)) '' RSet C 0 S :=
        ⟨support S, hS_in_R0, rfl⟩
      exact (Set.sInter_subset_of_mem hmem_im).trans (closure_subset_of_mem C hL hS_sub_L)
    have hQt_sub_L : robustQ C c h t.val S ⊆ L :=
      (robustQ_anti hh_ge1 S (Nat.zero_le t.val)).trans hQ0_sub_L
    have hcore_eq := blockCore_eq_at hnb ht_prof
    have hcore_ic_sub : blockCore C hnb N S σ ∈ infiniteClosure C ∧
        blockCore C hnb N S σ ⊆ robustQ C c h t.val S := by
      rw [hcore_eq]
      unfold barCore
      rw [if_pos hQ_ic]
      exact iterCore_mem_infiniteClosure hnb _ hQ_ic
    -- Therefore `resPart (blockCore σ) b j \ Set.range S` is infinite and `⊆ L \ Set.range S`!
    unfold upperOut
    dsimp only
    have hres_inf : (resPart (blockCore C hnb N S σ) b j).Infinite :=
      resPart_infinite hcore_ic_sub.1.1 hb_ge1 j
    have hrange_fin : (Set.range S).Finite := Set.finite_range S
    refine ⟨hres_inf.sdiff hrange_fin, ?_⟩
    exact Set.sdiff_subset_sdiff_left
      ((resPart_subset hcore_ic_sub.1.1 b j).trans (hcore_ic_sub.2.trans hQt_sub_L))

end UpperBound


/-! ### Part 4: Direct Interior-Point Lower Bound (Bun–Nissim–Stemmer–Vadhan 2015, Lemma 3.3) -/

section InteriorPointLowerBound

/-- `z` lies between the minimum and maximum entries of a nonempty tuple `y`. -/
def IsInterior {α : Type*} [Preorder α] {m : ℕ} (y : Fin m → α) (z : α) : Prop :=
  (∃ i : Fin m, y i ≤ z) ∧ (∃ j : Fin m, z ≤ y j)

/-- Domain tower `S(0) = B`, `S(k + 1) = B ^ S(k)`. -/
def bnsvS (B : ℕ) : ℕ → ℕ
  | 0 => B
  | k + 1 => B ^ bnsvS B k

lemma bnsvS_ge_B {B : ℕ} (hB : 2 ≤ B) : ∀ k : ℕ, B ≤ bnsvS B k
  | 0 => le_refl B
  | k + 1 => by
      have ih := bnsvS_ge_B hB k
      calc B = B ^ 1 := (pow_one B).symm
        _ ≤ B ^ bnsvS B k := Nat.pow_le_pow_right (by omega) (by omega)

/-- Big-endian base-`B` integer value of `d : Fin L → Fin B`. -/
def encodeDigits (B : ℕ) : ∀ L : ℕ, (Fin L → Fin B) → ℕ
  | 0, _ => 0
  | L + 1, d => (d 0).val * B ^ L + encodeDigits B L (fun j => d j.succ)

lemma encodeDigits_lt {B : ℕ} (hB : 1 ≤ B) :
    ∀ (L : ℕ) (d : Fin L → Fin B), encodeDigits B L d < B ^ L
  | 0, _ => by simp [encodeDigits]
  | L + 1, d => by
      simp only [encodeDigits]
      have hd0 : (d 0).val + 1 ≤ B := (d 0).isLt
      have hrem : encodeDigits B L (fun j => d j.succ) < B ^ L :=
        encodeDigits_lt hB L (fun j => d j.succ)
      have hmul : ((d 0).val + 1) * B ^ L ≤ B * B ^ L := Nat.mul_le_mul_right (B ^ L) hd0
      have hpow : B ^ (L + 1) = B * B ^ L := pow_succ' B L
      have hexp : ((d 0).val + 1) * B ^ L = (d 0).val * B ^ L + B ^ L := Nat.succ_mul _ _
      omega

/-- Inverse of `encodeDigits`: base-`B` digits of `z : Fin (B ^ L)`. -/
def decodeDigits (B : ℕ) (hB : 1 ≤ B) : ∀ L : ℕ, Fin (B ^ L) → (Fin L → Fin B)
  | 0, _ => fun j => j.elim0
  | L + 1, z =>
      have hBL_pos : 0 < B ^ L := Nat.pos_of_ne_zero (pow_ne_zero L (by omega))
      Fin.cons
        ⟨z.val / B ^ L, Nat.div_lt_of_lt_mul (by
          have hz := z.isLt
          have hp : B ^ (L + 1) = B ^ L * B := pow_succ B L
          omega)⟩
        (decodeDigits B hB L ⟨z.val % B ^ L, Nat.mod_lt z.val hBL_pos⟩)

lemma encode_decode {B : ℕ} (hB : 1 ≤ B) :
    ∀ (L : ℕ) (z : Fin (B ^ L)), encodeDigits B L (decodeDigits B hB L z) = z.val
  | 0, z => by
      have hz : z.val < 1 := z.isLt
      simp only [encodeDigits]
      omega
  | L + 1, z => by
      simp only [decodeDigits, encodeDigits, Fin.cons_succ]
      change (z.val / B ^ L) * B ^ L + encodeDigits B L (decodeDigits B hB L _) = z.val
      rw [encode_decode hB L]
      exact Nat.div_add_mod' z.val (B ^ L)

lemma decode_encode {B : ℕ} (hB : 1 ≤ B) :
    ∀ (L : ℕ) (d : Fin L → Fin B),
      decodeDigits B hB L ⟨encodeDigits B L d, encodeDigits_lt hB L d⟩ = d
  | 0, d => funext fun j => j.elim0
  | L + 1, d => by
      have hBL_pos : 0 < B ^ L := Nat.pos_of_ne_zero (pow_ne_zero L (by omega))
      have hr : encodeDigits B L (fun j => d j.succ) < B ^ L :=
        encodeDigits_lt hB L (fun j => d j.succ)
      have hdiv : ((d 0).val * B ^ L + encodeDigits B L (fun j => d j.succ)) / B ^ L = (d 0).val := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ hBL_pos, Nat.div_eq_of_lt hr, zero_add]
      have hmod : ((d 0).val * B ^ L + encodeDigits B L (fun j => d j.succ)) % B ^ L =
          encodeDigits B L (fun j => d j.succ) := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]
      funext j
      refine Fin.cases ?_ ?_ j
      · simp only [decodeDigits, encodeDigits, Fin.cons_zero]
        exact Fin.ext hdiv
      · intro j'
        simp only [decodeDigits, encodeDigits, Fin.cons_succ]
        have hsub : (⟨((d 0).val * B ^ L + encodeDigits B L (fun k => d k.succ)) % B ^ L,
            Nat.mod_lt _ hBL_pos⟩ : Fin (B ^ L)) =
            ⟨encodeDigits B L (fun k => d k.succ), hr⟩ := Fin.ext hmod
        rw [hsub, decode_encode hB L (fun k => d k.succ)]

/-- Prefix sandwich lemma: if `a` and `b` agree on indices `< m` and `encode a ≤ encode z ≤ encode b`,
    then `z` also agrees with `a` on indices `< m`. -/
lemma eq_of_encode_between {B : ℕ} (hB : 1 ≤ B) :
    ∀ {L : ℕ} {a b z : Fin L → Fin B} {m : ℕ},
      (∀ j : Fin L, j.val < m → a j = b j) →
      encodeDigits B L a ≤ encodeDigits B L z →
      encodeDigits B L z ≤ encodeDigits B L b →
      ∀ j : Fin L, j.val < m → z j = a j
  | 0, _, _, _, _, _, _, _, j, _ => j.elim0
  | L + 1, a, b, z, 0, _, _, _, j, hj => by omega
  | L + 1, a, b, z, m + 1, hab, haz, hzb, j, hj => by
      have hab0 : a 0 = b 0 := hab 0 (by simp)
      simp only [encodeDigits] at haz hzb
      rw [← hab0] at hzb
      have hta : encodeDigits B L (fun k => a k.succ) < B ^ L := encodeDigits_lt hB L _
      have htz : encodeDigits B L (fun k => z k.succ) < B ^ L := encodeDigits_lt hB L _
      have htb : encodeDigits B L (fun k => b k.succ) < B ^ L := encodeDigits_lt hB L _
      have hz0_ge : (a 0).val ≤ (z 0).val := by
        by_contra hlt
        have hle1 : (z 0).val + 1 ≤ (a 0).val := by omega
        have hmul : ((z 0).val + 1) * B ^ L ≤ (a 0).val * B ^ L := Nat.mul_le_mul_right _ hle1
        have hexp : ((z 0).val + 1) * B ^ L = (z 0).val * B ^ L + B ^ L := Nat.succ_mul _ _
        omega
      have hz0_le : (z 0).val ≤ (a 0).val := by
        by_contra hlt
        have hle1 : (a 0).val + 1 ≤ (z 0).val := by omega
        have hmul : ((a 0).val + 1) * B ^ L ≤ (z 0).val * B ^ L := Nat.mul_le_mul_right _ hle1
        have hexp : ((a 0).val + 1) * B ^ L = (a 0).val * B ^ L + B ^ L := Nat.succ_mul _ _
        omega
      have hz0_eq : z 0 = a 0 := Fin.ext (by omega)
      rw [hz0_eq] at haz hzb
      have htail_az : encodeDigits B L (fun k => a k.succ) ≤ encodeDigits B L (fun k => z k.succ) :=
        Nat.add_le_add_iff_left.mp haz
      have htail_zb : encodeDigits B L (fun k => z k.succ) ≤ encodeDigits B L (fun k => b k.succ) :=
        Nat.add_le_add_iff_left.mp hzb
      revert hj
      refine Fin.cases ?_ (fun j' hj' => ?_) j
      · intro _
        exact hz0_eq
      · rw [Fin.val_succ] at hj'
        exact eq_of_encode_between hB
          (fun k hk => hab k.succ (by rw [Fin.val_succ]; omega))
          htail_az htail_zb j' (Nat.lt_of_succ_lt_succ hj')

/-- Unclipped longest common prefix length of `d, y₀ : Fin L → Fin B`. -/
def lcpNat {B : ℕ} : ∀ {L : ℕ}, (Fin L → Fin B) → (Fin L → Fin B) → ℕ
  | 0, _, _ => 0
  | _ + 1, d, y₀ => if d 0 = y₀ 0 then 1 + lcpNat (fun j => d j.succ) (fun j => y₀ j.succ) else 0

lemma le_lcpNat_of_prefix {B : ℕ} :
    ∀ {L m : ℕ} {d y₀ : Fin L → Fin B},
      m ≤ L → (∀ j : Fin L, j.val < m → d j = y₀ j) → m ≤ lcpNat d y₀
  | _, 0, _, _, _, _ => Nat.zero_le _
  | 0, m + 1, _, _, hm, _ => by omega
  | L + 1, m + 1, d, y₀, hm, hpref => by
      have h0 : d 0 = y₀ 0 := hpref 0 (by simp)
      simp only [lcpNat, if_pos h0]
      have ih := le_lcpNat_of_prefix (L := L) (m := m) (by omega)
        (fun j hj => hpref j.succ (by rw [Fin.val_succ]; omega))
      omega

lemma eq_at_of_lt_lcpNat {B : ℕ} :
    ∀ {L : ℕ} {d y₀ : Fin L → Fin B} (w : Fin L),
      w.val < lcpNat d y₀ → d w = y₀ w
  | 0, _, _, w, _ => w.elim0
  | L + 1, d, y₀, w, hw => by
      simp only [lcpNat] at hw
      split_ifs at hw with h0
      · revert hw
        refine Fin.cases ?_ (fun w' hw' => ?_) w
        · intro _; exact h0
        · rw [Fin.val_succ, Nat.add_comm 1] at hw'
          exact eq_at_of_lt_lcpNat w' (Nat.lt_of_add_lt_add_right hw')
      · omega

def lcpClipped {B L : ℕ} (hL : 1 ≤ L) (d y₀ : Fin L → Fin B) : Fin L :=
  ⟨min (L - 1) (lcpNat d y₀), by omega⟩

/-- Involution `(f, v) ↦ (Function.update f w v, f w)` for coordinate resampling. -/
def swapAt {α β : Type*} [DecidableEq α] (w : α) (p : (α → β) × β) : (α → β) × β :=
  (Function.update p.1 w p.2, p.1 w)

lemma swapAt_involutive {α β : Type*} [DecidableEq α] (w : α) :
    Function.Involutive (swapAt (β := β) w) := by
  rintro ⟨f, v⟩
  unfold swapAt
  dsimp only
  ext1
  · ext a
    by_cases ha : a = w
    · subst ha; simp
    · simp [ha]
  · simp

def swapAtEquiv {α β : Type*} [DecidableEq α] (w : α) : ((α → β) × β) ≃ ((α → β) × β) :=
  ⟨swapAt w, swapAt w, swapAt_involutive w, swapAt_involutive w⟩

/-- Inductive BNSV tuple construction from `x : Fin (k + 1) → Fin L`. -/
def makeDigits {B L k : ℕ} (x : Fin (k + 1) → Fin L)
    (y₀ : Fin L → Fin B) (u : Fin (k + 1) → Fin L → Fin B) :
    Fin (k + 2) → (Fin L → Fin B) :=
  Fin.cons y₀ fun i j => if j.val < (x i).val then y₀ j else u i j

def makeY {B L k : ℕ} (hB : 1 ≤ B) (x : Fin (k + 1) → Fin L)
    (y₀ : Fin L → Fin B) (u : Fin (k + 1) → Fin L → Fin B) :
    Fin (k + 2) → Fin (B ^ L) :=
  fun t => ⟨encodeDigits B L (makeDigits x y₀ u t), encodeDigits_lt hB L _⟩

lemma interior_makeY_subset {B L k : ℕ} (hB : 1 ≤ B) (hL : 1 ≤ L)
    (x : Fin (k + 1) → Fin L) (y₀ : Fin L → Fin B) (u : Fin (k + 1) → Fin L → Fin B)
    (z : Fin (B ^ L)) (hint : IsInterior (makeY hB x y₀ u) z) :
    IsInterior x (lcpClipped hL (decodeDigits B hB L z) y₀) ∨
      decodeDigits B hB L z ((Finset.univ.image x).max' (by simp)) =
        y₀ ((Finset.univ.image x).max' (by simp)) := by
  have himg_ne : (Finset.univ.image x).Nonempty := by simp
  set v_min := (Finset.univ.image x).min' himg_ne
  set w := (Finset.univ.image x).max' himg_ne
  obtain ⟨i_min, _, hi_min⟩ := Finset.mem_image.mp (Finset.min'_mem _ himg_ne)
  obtain ⟨j_max, _, hj_max⟩ := Finset.mem_image.mp (Finset.max'_mem _ himg_ne)
  have hv_le : ∀ i : Fin (k + 1), v_min ≤ x i := fun i =>
    Finset.min'_le _ (x i) (Finset.mem_image_of_mem x (Finset.mem_univ i))
  -- Every `makeDigits x y₀ u t` agrees with `y₀` on indices `< v_min.val`.
  have hagree : ∀ (t : Fin (k + 2)) (j : Fin L), j.val < v_min.val →
      makeDigits x y₀ u t j = y₀ j := by
    intro t
    refine Fin.cases ?_ (fun i j hj => ?_) t
    · intro _ _; rfl
    · simp only [makeDigits, Fin.cons_succ]
      have hji : j.val < (x i).val := lt_of_lt_of_le hj (Fin.le_iff_val_le_val.mp (hv_le i))
      exact if_pos hji
  obtain ⟨⟨t₁, ht₁⟩, ⟨t₂, ht₂⟩⟩ := hint
  have haz : encodeDigits B L (makeDigits x y₀ u t₁) ≤
      encodeDigits B L (decodeDigits B hB L z) := by
    rw [encode_decode hB L z]
    exact Fin.le_iff_val_le_val.mp ht₁
  have hzb : encodeDigits B L (decodeDigits B hB L z) ≤
      encodeDigits B L (makeDigits x y₀ u t₂) := by
    rw [encode_decode hB L z]
    exact Fin.le_iff_val_le_val.mp ht₂
  have hz_pref : ∀ j : Fin L, j.val < v_min.val → decodeDigits B hB L z j = y₀ j := by
    intro j hj
    have h1 := eq_of_encode_between hB
      (fun j' hj' => (hagree t₁ j' hj').trans (hagree t₂ j' hj').symm) haz hzb j hj
    exact h1.trans (hagree t₁ j hj)
  have hlcp_ge : v_min ≤ lcpClipped hL (decodeDigits B hB L z) y₀ := by
    rw [Fin.le_iff_val_le_val]
    unfold lcpClipped
    simp only [le_min_iff]
    refine ⟨by omega, le_lcpNat_of_prefix (by omega) hz_pref⟩
  have hxmin_le : x i_min ≤ lcpClipped hL (decodeDigits B hB L z) y₀ := hi_min ▸ hlcp_ge
  by_cases hub : ∃ j : Fin (k + 1), lcpClipped hL (decodeDigits B hB L z) y₀ ≤ x j
  · exact Or.inl ⟨⟨i_min, hxmin_le⟩, hub⟩
  · right
    have hw_lt : w < lcpClipped hL (decodeDigits B hB L z) y₀ := by
      have hj_max_w : x j_max = w := hj_max
      rw [← hj_max_w]
      exact lt_of_not_ge fun hge => hub ⟨j_max, hge⟩
    have hw_val_lt : w.val < lcpNat (decodeDigits B hB L z) y₀ := by
      have hv := Fin.lt_iff_val_lt_val.mp hw_lt
      unfold lcpClipped at hv
      dsimp only at hv
      omega
    exact eq_at_of_lt_lcpNat w hw_val_lt

/-- Explicit seed type `Ω_k` and generator `gen_k` for BNSV Lemma 3.3. -/
def bnsvSeed (B : ℕ) : ℕ → Type
  | 0 => Fin B
  | k + 1 => bnsvSeed B k × ((Fin (bnsvS B k) → Fin B) × (Fin (k + 1) → Fin (bnsvS B k) → Fin B))

instance bnsvSeed_fintype (B : ℕ) : ∀ k : ℕ, Fintype (bnsvSeed B k)
  | 0 => by unfold bnsvSeed; infer_instance
  | k + 1 => by
      unfold bnsvSeed
      letI := bnsvSeed_fintype B k
      infer_instance

lemma bnsvSeed_nonempty {B : ℕ} (hB : 1 ≤ B) : ∀ k : ℕ, Nonempty (bnsvSeed B k)
  | 0 => ⟨⟨0, hB⟩⟩
  | k + 1 => by
      unfold bnsvSeed
      obtain ⟨ω₀⟩ := bnsvSeed_nonempty hB k
      exact ⟨(ω₀, (fun _ => ⟨0, hB⟩, fun _ _ => ⟨0, hB⟩))⟩

def bnsvGen {B : ℕ} (hB : 1 ≤ B) : ∀ k : ℕ, bnsvSeed B k → (Fin (k + 1) → Fin (bnsvS B k))
  | 0, b => fun _ => b
  | k + 1, (ω, (y₀, u)) => makeY hB (bnsvGen hB k ω) y₀ u

/-- Inductive step of Lemma 3.3 of [BNSV15], parameterized by `L : ℕ` so `B ^ L` is syntactic. -/
lemma bnsv_step_bound {B L k : ℕ} (hB1 : 1 ≤ B) (hL1 : 1 ≤ L)
    {Ω : Type} [Fintype Ω] [Nonempty Ω] (gen : Ω → (Fin (k + 1) → Fin L))
    {δ : ℝ} (hδ : 0 ≤ δ)
    (ih : ∀ (Mred : Mechanism (Fin L) (Fin L) (k + 1)), IsDP Mred 1 δ →
      ((Fintype.card Ω : ℝ)⁻¹) *
        (∑ ω : Ω, (Mred (gen ω) : Measure (Fin L)).real {v | IsInterior (gen ω) v}) ≤
        ((k + 1 : ℕ) : ℝ) * (Real.exp 1 / (B : ℝ) + δ))
    (Mhat : Mechanism (Fin (B ^ L)) (Fin (B ^ L)) (k + 2)) (hdp : IsDP Mhat 1 δ) :
    let Θ := (Fin L → Fin B) × (Fin (k + 1) → Fin L → Fin B)
    ((Fintype.card (Ω × Θ) : ℝ)⁻¹) *
      (∑ p : Ω × Θ,
        (Mhat (makeY hB1 (gen p.1) p.2.1 p.2.2) : Measure (Fin (B ^ L))).real
          {z | IsInterior (makeY hB1 (gen p.1) p.2.1 p.2.2) z}) ≤
      ((k + 2 : ℕ) : ℝ) * (Real.exp 1 / (B : ℝ) + δ) := by
  intro Θ
  have : Nonempty Θ := ⟨(fun _ => ⟨0, hB1⟩, fun _ _ => ⟨0, hB1⟩)⟩
  let decF : Θ → Fin (B ^ L) → Fin L := fun θ z =>
    lcpClipped hL1 (decodeDigits B hB1 L z) θ.1
  have hdec_meas : ∀ θ : Θ, Measurable (decF θ) := fun _ => measurable_of_finite _
  let encF : Θ → (Fin (k + 1) → Fin L) → (Fin (k + 2) → Fin (B ^ L)) := fun θ x =>
    makeY hB1 x θ.1 θ.2
  have henc_near : ∀ (θ : Θ) {x x' : Fin (k + 1) → Fin L},
      Neighbors x x' → Near (encF θ x) (encF θ x') := by
    intro θ x x' ⟨i₀, _, hrest⟩
    refine near_of_eq_except i₀.succ fun t ht => ?_
    revert ht
    refine Fin.cases ?_ (fun i hi => ?_) t
    · intro _; rfl
    · have hi_ne : i ≠ i₀ := fun heq => hi (congrArg Fin.succ heq)
      simp only [encF, makeY, makeDigits, Fin.cons_succ, hrest i hi_ne]
  let Mred : Mechanism (Fin L) (Fin L) (k + 1) := fun x =>
    avgMapPM (fun θ : Θ => Mhat (encF θ x)) decF hdec_meas
  have hMred_dp : IsDP Mred 1 δ :=
    isDP_avgMap Mhat hdp (by norm_num) hδ encF henc_near decF hdec_meas
  have ih_bound := ih Mred hMred_dp
  have hunion_pt : ∀ (ω : Ω) (θ : Θ),
      (Mhat (makeY hB1 (gen ω) θ.1 θ.2) : Measure (Fin (B ^ L))).real
          {z | IsInterior (makeY hB1 (gen ω) θ.1 θ.2) z} ≤
        (Mhat (encF θ (gen ω)) : Measure (Fin (B ^ L))).real
          (decF θ ⁻¹' {v | IsInterior (gen ω) v}) +
        (Mhat (makeY hB1 (gen ω) θ.1 θ.2) : Measure (Fin (B ^ L))).real
          {z | decodeDigits B hB1 L z ((Finset.univ.image (gen ω)).max' (by simp)) =
            θ.1 ((Finset.univ.image (gen ω)).max' (by simp))} := by
    intro ω θ
    set x := gen ω
    set w := (Finset.univ.image x).max' (by simp)
    let E₁ : Set (Fin (B ^ L)) := decF θ ⁻¹' {v | IsInterior x v}
    let E₂ : Set (Fin (B ^ L)) := {z | decodeDigits B hB1 L z w = θ.1 w}
    have hsub : {z | IsInterior (makeY hB1 x θ.1 θ.2) z} ⊆ E₁ ∪ E₂ := fun z hz =>
      interior_makeY_subset hB1 hL1 x θ.1 θ.2 z hz
    calc (Mhat (makeY hB1 x θ.1 θ.2) : Measure _).real {z | IsInterior (makeY hB1 x θ.1 θ.2) z}
        ≤ (Mhat (makeY hB1 x θ.1 θ.2) : Measure _).real (E₁ ∪ E₂) :=
          measureReal_mono hsub
      _ ≤ (Mhat (makeY hB1 x θ.1 θ.2) : Measure _).real E₁ +
          (Mhat (makeY hB1 x θ.1 θ.2) : Measure _).real E₂ :=
          measureReal_union_le E₁ E₂
  have hguess_bound : ∀ (x : Fin (k + 1) → Fin L) (u : Fin (k + 1) → Fin L → Fin B),
      let w := (Finset.univ.image x).max' (by simp)
      ∑ y₀ : Fin L → Fin B,
        (Mhat (makeY hB1 x y₀ u) : Measure (Fin (B ^ L))).real
          {z | decodeDigits B hB1 L z w = y₀ w} ≤
        (Fintype.card (Fin L → Fin B) : ℝ) * (Real.exp 1 / (B : ℝ) + δ) := by
    intro x u w
    have hw_ge : ∀ i : Fin (k + 1), x i ≤ w := fun i =>
      Finset.le_max' _ (x i) (Finset.mem_image_of_mem x (Finset.mem_univ i))
    have hB_pos : (0 : ℝ) < (B : ℝ) := by positivity
    have hB_ne : (B : ℝ) ≠ 0 := hB_pos.ne'
    have hmul_B : (B : ℝ) * (∑ y₀ : Fin L → Fin B,
          (Mhat (makeY hB1 x y₀ u) : Measure _).real {z | decodeDigits B hB1 L z w = y₀ w}) =
        ∑ y₀ : Fin L → Fin B, ∑ v : Fin B,
          (Mhat (makeY hB1 x (Function.update y₀ w v) u) : Measure _).real
            {z | decodeDigits B hB1 L z w = v} := by
      have hconst : (B : ℝ) * (∑ y₀ : Fin L → Fin B,
            (Mhat (makeY hB1 x y₀ u) : Measure _).real {z | decodeDigits B hB1 L z w = y₀ w}) =
          ∑ p : (Fin L → Fin B) × Fin B,
            (Mhat (makeY hB1 x p.1 u) : Measure _).real {z | decodeDigits B hB1 L z w = p.1 w} := by
        rw [Fintype.sum_prod_type]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [← Finset.mul_sum]
      rw [hconst, ← Equiv.sum_comp (swapAtEquiv w), Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun y₀ _ => Finset.sum_congr rfl fun v _ => ?_
      have hupd : (swapAtEquiv w (y₀, v)).1 = Function.update y₀ w v := rfl
      rw [hupd, Function.update_self]
    have hinner_le : ∀ y₀ : Fin L → Fin B,
        (∑ v : Fin B, (Mhat (makeY hB1 x (Function.update y₀ w v) u) : Measure _).real
            {z | decodeDigits B hB1 L z w = v}) ≤
          Real.exp 1 + (B : ℝ) * δ := by
      intro y₀
      have hnear_v : ∀ v : Fin B, Near (makeY hB1 x (Function.update y₀ w v) u) (makeY hB1 x y₀ u) := by
        intro v
        refine near_of_eq_except 0 fun t ht => ?_
        revert ht
        refine Fin.cases (fun h0 => absurd rfl h0) (fun i _ => ?_) t
        simp only [makeY, makeDigits, Fin.cons_succ]
        congr 2
        ext j
        split_ifs with hj
        · have hj_lt_w : j.val < w.val :=
            lt_of_lt_of_le hj (Fin.le_iff_val_le_val.mp (hw_ge i))
          have hjw : j ≠ w := fun heq => by subst heq; exact Nat.lt_irrefl _ hj_lt_w
          exact congrArg Fin.val (Function.update_of_ne hjw v y₀)
        · rfl
      have hdp_v : ∀ v : Fin B,
          (Mhat (makeY hB1 x (Function.update y₀ w v) u) : Measure _).real
              {z | decodeDigits B hB1 L z w = v} ≤
            Real.exp 1 * (Mhat (makeY hB1 x y₀ u) : Measure _).real
              {z | decodeDigits B hB1 L z w = v} + δ := fun v =>
        isDP_near_le hdp (by norm_num) hδ (hnear_v v) (DiscreteMeasurableSpace.forall_measurableSet _)
      have hpart_le1 : ∑ v : Fin B,
          (Mhat (makeY hB1 x y₀ u) : Measure _).real {z | decodeDigits B hB1 L z w = v} ≤ 1 :=
        sum_disjoint_real_le_one (Mhat (makeY hB1 x y₀ u))
          (fun v => {z | decodeDigits B hB1 L z w = v})
          (fun _ => DiscreteMeasurableSpace.forall_measurableSet _)
          (fun v₁ v₂ hne => Set.disjoint_left.mpr fun z hz1 hz2 => hne (hz1.symm.trans hz2))
      have hexp_part := mul_le_mul_of_nonneg_left hpart_le1 (Real.exp_pos 1).le
      calc ∑ v : Fin B, (Mhat (makeY hB1 x (Function.update y₀ w v) u) : Measure _).real
              {z | decodeDigits B hB1 L z w = v}
          ≤ ∑ v : Fin B, (Real.exp 1 * (Mhat (makeY hB1 x y₀ u) : Measure _).real
              {z | decodeDigits B hB1 L z w = v} + δ) := Finset.sum_le_sum fun v _ => hdp_v v
        _ = Real.exp 1 * (∑ v : Fin B, (Mhat (makeY hB1 x y₀ u) : Measure _).real
              {z | decodeDigits B hB1 L z w = v}) + (B : ℝ) * δ := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
              Fintype.card_fin, nsmul_eq_mul]
        _ ≤ Real.exp 1 + (B : ℝ) * δ := by linarith
    have hsum_y0 : (B : ℝ) * (∑ y₀ : Fin L → Fin B,
          (Mhat (makeY hB1 x y₀ u) : Measure _).real {z | decodeDigits B hB1 L z w = y₀ w}) ≤
        (Fintype.card (Fin L → Fin B) : ℝ) * (Real.exp 1 + (B : ℝ) * δ) := by
      rw [hmul_B]
      calc ∑ y₀ : Fin L → Fin B, ∑ v : Fin B,
              (Mhat (makeY hB1 x (Function.update y₀ w v) u) : Measure _).real
                {z | decodeDigits B hB1 L z w = v}
          ≤ ∑ _y₀ : Fin L → Fin B, (Real.exp 1 + (B : ℝ) * δ) :=
            Finset.sum_le_sum fun y₀ _ => hinner_le y₀
        _ = (Fintype.card (Fin L → Fin B) : ℝ) * (Real.exp 1 + (B : ℝ) * δ) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hdiv := mul_le_mul_of_nonneg_left hsum_y0 (inv_nonneg.mpr hB_pos.le)
    calc ∑ y₀ : Fin L → Fin B,
            (Mhat (makeY hB1 x y₀ u) : Measure _).real {z | decodeDigits B hB1 L z w = y₀ w}
        = ((B : ℝ)⁻¹) * ((B : ℝ) * ∑ y₀ : Fin L → Fin B,
            (Mhat (makeY hB1 x y₀ u) : Measure _).real {z | decodeDigits B hB1 L z w = y₀ w}) := by
          field_simp [hB_ne]
      _ ≤ ((B : ℝ)⁻¹) * ((Fintype.card (Fin L → Fin B) : ℝ) * (Real.exp 1 + (B : ℝ) * δ)) := hdiv
      _ = (Fintype.card (Fin L → Fin B) : ℝ) * (Real.exp 1 / (B : ℝ) + δ) := by
          field_simp [hB_ne]
  have hcardΘ_pos : (0 : ℝ) < (Fintype.card Θ : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hcardΩ_pos : (0 : ℝ) < (Fintype.card Ω : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hsum_θ : ∀ ω : Ω,
      ((Fintype.card Θ : ℝ)⁻¹) * (∑ θ : Θ,
        (Mhat (makeY hB1 (gen ω) θ.1 θ.2) : Measure _).real
          {z | IsInterior (makeY hB1 (gen ω) θ.1 θ.2) z}) ≤
      (Mred (gen ω) : Measure (Fin L)).real {v | IsInterior (gen ω) v} +
        (Real.exp 1 / (B : ℝ) + δ) := by
    intro ω
    have hMred_eq : (Mred (gen ω) : Measure (Fin L)).real {v | IsInterior (gen ω) v} =
        ((Fintype.card Θ : ℝ)⁻¹) * ∑ θ : Θ,
          (Mhat (encF θ (gen ω)) : Measure _).real (decF θ ⁻¹' {v | IsInterior (gen ω) v}) :=
      avgMapPM_real_apply _ _ _ (DiscreteMeasurableSpace.forall_measurableSet _)
    have h2nd_θ : ((Fintype.card Θ : ℝ)⁻¹) * (∑ θ : Θ,
          (Mhat (makeY hB1 (gen ω) θ.1 θ.2) : Measure _).real
            {z | decodeDigits B hB1 L z ((Finset.univ.image (gen ω)).max' (by simp)) =
              θ.1 ((Finset.univ.image (gen ω)).max' (by simp))}) ≤
        Real.exp 1 / (B : ℝ) + δ := by
      have hcardΘ_eq : (Fintype.card Θ : ℝ) =
          (Fintype.card (Fin L → Fin B) : ℝ) *
            (Fintype.card (Fin (k + 1) → Fin L → Fin B) : ℝ) := by
        dsimp [Θ]; rw [Fintype.card_prod, Nat.cast_mul]
      have hsum_u : ∑ θ : Θ,
          (Mhat (makeY hB1 (gen ω) θ.1 θ.2) : Measure _).real
            {z | decodeDigits B hB1 L z ((Finset.univ.image (gen ω)).max' (by simp)) =
              θ.1 ((Finset.univ.image (gen ω)).max' (by simp))} ≤
          (Fintype.card Θ : ℝ) * (Real.exp 1 / (B : ℝ) + δ) := by
        dsimp [Θ]
        rw [Fintype.sum_prod_type_right]
        calc ∑ u : Fin (k + 1) → Fin L → Fin B, ∑ y₀ : Fin L → Fin B,
                (Mhat (makeY hB1 (gen ω) y₀ u) : Measure _).real
                  {z | decodeDigits B hB1 L z ((Finset.univ.image (gen ω)).max' (by simp)) =
                    y₀ ((Finset.univ.image (gen ω)).max' (by simp))}
            ≤ ∑ _u : Fin (k + 1) → Fin L → Fin B,
                (Fintype.card (Fin L → Fin B) : ℝ) * (Real.exp 1 / (B : ℝ) + δ) :=
              Finset.sum_le_sum fun u _ => hguess_bound (gen ω) u
          _ = (Fintype.card Θ : ℝ) * (Real.exp 1 / (B : ℝ) + δ) := by
              rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcardΘ_eq]
              ring
      have hneΘ : (Fintype.card Θ : ℝ) ≠ 0 := hcardΘ_pos.ne'
      calc ((Fintype.card Θ : ℝ)⁻¹) * ∑ θ : Θ, _
          ≤ ((Fintype.card Θ : ℝ)⁻¹) * ((Fintype.card Θ : ℝ) * (Real.exp 1 / (B : ℝ) + δ)) :=
            mul_le_mul_of_nonneg_left hsum_u (inv_nonneg.mpr hcardΘ_pos.le)
        _ = Real.exp 1 / (B : ℝ) + δ := by field_simp [hneΘ]
    calc ((Fintype.card Θ : ℝ)⁻¹) * ∑ θ : Θ, _
        ≤ ((Fintype.card Θ : ℝ)⁻¹) * ∑ θ : Θ,
            ((Mhat (encF θ (gen ω)) : Measure _).real (decF θ ⁻¹' {v | IsInterior (gen ω) v}) +
             (Mhat (makeY hB1 (gen ω) θ.1 θ.2) : Measure _).real
              {z | decodeDigits B hB1 L z ((Finset.univ.image (gen ω)).max' (by simp)) =
                θ.1 ((Finset.univ.image (gen ω)).max' (by simp))}) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun θ _ => hunion_pt ω θ)
            (inv_nonneg.mpr hcardΘ_pos.le)
      _ = ((Fintype.card Θ : ℝ)⁻¹) * (∑ θ : Θ,
            (Mhat (encF θ (gen ω)) : Measure _).real (decF θ ⁻¹' {v | IsInterior (gen ω) v})) +
          ((Fintype.card Θ : ℝ)⁻¹) * (∑ θ : Θ,
            (Mhat (makeY hB1 (gen ω) θ.1 θ.2) : Measure _).real
              {z | decodeDigits B hB1 L z ((Finset.univ.image (gen ω)).max' (by simp)) =
                θ.1 ((Finset.univ.image (gen ω)).max' (by simp))}) := by
          rw [Finset.sum_add_distrib, mul_add]
      _ ≤ (Mred (gen ω) : Measure (Fin L)).real {v | IsInterior (gen ω) v} +
            (Real.exp 1 / (B : ℝ) + δ) := by
          rw [← hMred_eq]; linarith
  have hrewrite_outer : ((Fintype.card (Ω × Θ) : ℝ)⁻¹) *
        (∑ p : Ω × Θ,
          (Mhat (makeY hB1 (gen p.1) p.2.1 p.2.2) : Measure _).real
            {z | IsInterior (makeY hB1 (gen p.1) p.2.1 p.2.2) z}) =
      ((Fintype.card Ω : ℝ)⁻¹) *
        ∑ ω : Ω, ((Fintype.card Θ : ℝ)⁻¹) *
          ∑ θ : Θ, (Mhat (makeY hB1 (gen ω) θ.1 θ.2) : Measure _).real
            {z | IsInterior (makeY hB1 (gen ω) θ.1 θ.2) z} := by
    rw [Fintype.card_prod, Nat.cast_mul, mul_inv, Fintype.sum_prod_type, Finset.mul_sum]
    simp_rw [mul_assoc, Finset.mul_sum]
  rw [hrewrite_outer]
  calc ((Fintype.card Ω : ℝ)⁻¹) *
          ∑ ω : Ω, ((Fintype.card Θ : ℝ)⁻¹) *
            ∑ θ : Θ, (Mhat (makeY hB1 (gen ω) θ.1 θ.2) : Measure _).real
              {z | IsInterior (makeY hB1 (gen ω) θ.1 θ.2) z}
      ≤ ((Fintype.card Ω : ℝ)⁻¹) *
          ∑ ω : Ω, ((Mred (gen ω) : Measure (Fin L)).real {v | IsInterior (gen ω) v} +
            (Real.exp 1 / (B : ℝ) + δ)) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun ω _ => hsum_θ ω)
          (inv_nonneg.mpr hcardΩ_pos.le)
    _ = ((Fintype.card Ω : ℝ)⁻¹) *
          (∑ ω : Ω, (Mred (gen ω) : Measure (Fin L)).real {v | IsInterior (gen ω) v}) +
          (Real.exp 1 / (B : ℝ) + δ) := by
        have hneΩ : (Fintype.card Ω : ℝ) ≠ 0 := hcardΩ_pos.ne'
        rw [Finset.sum_add_distrib, mul_add, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        field_simp [hneΩ]
    _ ≤ ((k + 1 : ℕ) : ℝ) * (Real.exp 1 / (B : ℝ) + δ) + (Real.exp 1 / (B : ℝ) + δ) := by
        linarith [ih_bound]
    _ = ((k + 2 : ℕ) : ℝ) * (Real.exp 1 / (B : ℝ) + δ) := by
        push_cast; ring

lemma bnsv_base_bound {B : ℕ} (hB1 : 1 ≤ B) {δ : ℝ} (hδ : 0 ≤ δ)
    (M : Mechanism (Fin B) (Fin B) 1) (hdp : IsDP M 1 δ) :
    ((Fintype.card (Fin B) : ℝ)⁻¹) *
      (∑ b : Fin B,
        (M (fun _ : Fin 1 => b) : Measure (Fin B)).real
          {z : Fin B | IsInterior (fun _ : Fin 1 => b) z}) ≤
      ((1 : ℕ) : ℝ) * (Real.exp 1 / (B : ℝ) + δ) := by
  rw [Fintype.card_fin]
  push_cast
  rw [one_mul]
  let b₀ : Fin B := ⟨0, hB1⟩
  have hint_eq : ∀ b : Fin B, {z : Fin B | IsInterior (fun _ : Fin 1 => b) z} = {b} := by
    intro b
    ext z
    simp only [IsInterior, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨_, h1⟩, ⟨_, h2⟩⟩
      exact le_antisymm h2 h1
    · rintro rfl
      exact ⟨⟨0, le_refl _⟩, ⟨0, le_refl _⟩⟩
  have hterm : ∀ b : Fin B,
      (M (fun _ => b) : Measure (Fin B)).real {b} ≤
        Real.exp 1 * (M (fun _ => b₀) : Measure (Fin B)).real {b} + δ := by
    intro b
    have hnear : Near (fun _ : Fin 1 => b) (fun _ : Fin 1 => b₀) :=
      near_of_eq_except 0 fun j hj => absurd (Subsingleton.elim j 0) hj
    exact isDP_near_le hdp (by norm_num) hδ hnear (MeasurableSet.singleton b)
  have hsum_b0 : ∑ b : Fin B, (M (fun _ => b₀) : Measure (Fin B)).real {b} ≤ 1 :=
    sum_disjoint_real_le_one (M (fun _ => b₀)) (fun b => {b})
      (fun b => MeasurableSet.singleton b)
      (fun b₁ b₂ hne => Set.disjoint_singleton.mpr hne)
  have hexp_b0 := mul_le_mul_of_nonneg_left hsum_b0 (Real.exp_pos 1).le
  have hsum_all : ∑ b : Fin B, (M (fun _ => b) : Measure (Fin B)).real
        {z | IsInterior (fun _ : Fin 1 => b) z} ≤ Real.exp 1 + (B : ℝ) * δ := by
    simp_rw [hint_eq]
    calc ∑ b : Fin B, (M (fun _ => b) : Measure (Fin B)).real {b}
        ≤ ∑ b : Fin B, (Real.exp 1 * (M (fun _ => b₀) : Measure (Fin B)).real {b} + δ) :=
          Finset.sum_le_sum fun b _ => hterm b
      _ = Real.exp 1 * (∑ b : Fin B, (M (fun _ => b₀) : Measure (Fin B)).real {b}) +
            (B : ℝ) * δ := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul]
      _ ≤ Real.exp 1 + (B : ℝ) * δ := by linarith
  have hB_pos : (0 : ℝ) < (B : ℝ) := by positivity
  have hB_ne : (B : ℝ) ≠ 0 := hB_pos.ne'
  calc ((B : ℝ)⁻¹) * ∑ b : Fin B,
          (M (fun _ => b) : Measure (Fin B)).real {z | IsInterior (fun _ : Fin 1 => b) z}
      ≤ ((B : ℝ)⁻¹) * (Real.exp 1 + (B : ℝ) * δ) :=
        mul_le_mul_of_nonneg_left hsum_all (inv_nonneg.mpr hB_pos.le)
    _ = Real.exp 1 / (B : ℝ) + δ := by field_simp [hB_ne]

/-- Lemma 3.3 of [BNSV15]: Induction on `k` bounding average interior-point success probability. -/
lemma bnsv_avg_bound {B : ℕ} (hB : 2 ≤ B) :
    ∀ (k : ℕ) {δ : ℝ} (_ : 0 ≤ δ)
      (M : Mechanism (Fin (bnsvS B k)) (Fin (bnsvS B k)) (k + 1))
      (_ : IsDP M 1 δ),
      ((Fintype.card (bnsvSeed B k) : ℝ)⁻¹) *
        (∑ ω : bnsvSeed B k,
          (M (bnsvGen (by omega) k ω) : Measure (Fin (bnsvS B k))).real
            {z | IsInterior (bnsvGen (by omega) k ω) z}) ≤
        ((k + 1 : ℕ) : ℝ) * (Real.exp 1 / (B : ℝ) + δ) := by
  have hB1 : 1 ≤ B := by omega
  intro k
  induction k with
  | zero =>
      intro δ hδ M hdp
      exact bnsv_base_bound hB1 hδ M hdp
  | succ k ih =>
      intro δ hδ Mhat hdp
      have hL1 : 1 ≤ bnsvS B k := le_trans hB1 (le_trans (by omega) (bnsvS_ge_B hB k))
      have : Nonempty (bnsvSeed B k) := bnsvSeed_nonempty hB1 k
      exact bnsv_step_bound hB1 hL1 (bnsvGen hB1 k) hδ (fun Mred hMred => ih hδ Mred hMred) Mhat hdp

/-- Unified impossibility of `(1, δ)`-DP interior point with success `≥ 2/3` when `m * δ ≤ 1/10`.
    Replaces both Lemma 6.4 and Lemma 6.9 of the paper! -/
theorem no_dp_interior_point {m : ℕ} (hm : 1 ≤ m) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ : (m : ℝ) * δ ≤ 1 / 10) :
    let N := bnsvS (100 * m) (m - 1)
    2 ≤ N ∧ ¬ ∃ M : Mechanism (Fin N) (Fin N) m, IsDP M 1 δ ∧
      ∀ y : Fin m → Fin N,
        2 / 3 ≤ (M y : Measure (Fin N)).real {z | IsInterior y z} := by
  set B := 100 * m
  have hB2 : 2 ≤ B := by dsimp [B]; omega
  set k := m - 1
  have hk_succ : k + 1 = m := by omega
  refine ⟨hB2.trans (bnsvS_ge_B hB2 k), ?_⟩
  rintro ⟨M, hdp, hacc⟩
  -- Transport `M` along `k + 1 = m`.
  let M' : Mechanism (Fin (bnsvS B k)) (Fin (bnsvS B k)) (k + 1) := fun y =>
    M (y ∘ Fin.cast hk_succ.symm)
  have hdp' : IsDP M' 1 δ := by
    intro S S' ⟨i₀, hne, hrest⟩ O hO
    refine hdp _ _ ⟨Fin.cast hk_succ i₀, ?_, ?_⟩ O hO
    · simpa [Function.comp] using hne
    · intro j hj
      have hj' : Fin.cast hk_succ.symm j ≠ i₀ := fun heq =>
        hj (by rw [← heq]; simp)
      exact hrest _ hj'
  have havg_ub := bnsv_avg_bound hB2 k hδ0 M' hdp'
  -- Every `ω` has success `≥ 2 / 3` under `M'`!
  have hB1 : 1 ≤ B := by omega
  have : Nonempty (bnsvSeed B k) := bnsvSeed_nonempty hB1 k
  have hpt_lb : ∀ ω : bnsvSeed B k,
      2 / 3 ≤ (M' (bnsvGen hB1 k ω) : Measure (Fin (bnsvS B k))).real
        {z | IsInterior (bnsvGen hB1 k ω) z} := by
    intro ω
    let y' := bnsvGen hB1 k ω
    let y : Fin m → Fin (bnsvS B k) := y' ∘ Fin.cast hk_succ.symm
    have hset : {z | IsInterior y z} = {z | IsInterior y' z} := by
      ext z
      simp only [IsInterior, y, Function.comp_apply]
      constructor
      · rintro ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
        exact ⟨⟨Fin.cast hk_succ.symm i, hi⟩, ⟨Fin.cast hk_succ.symm j, hj⟩⟩
      · rintro ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
        exact ⟨⟨Fin.cast hk_succ i, by simpa using hi⟩, ⟨Fin.cast hk_succ j, by simpa using hj⟩⟩
    have := hacc y
    rw [hset] at this
    exact this
  have hcard_pos : (0 : ℝ) < (Fintype.card (bnsvSeed B k) : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hcard_ne : (Fintype.card (bnsvSeed B k) : ℝ) ≠ 0 := hcard_pos.ne'
  have hsum_lb : (Fintype.card (bnsvSeed B k) : ℝ) * (2 / 3) ≤
      ∑ ω : bnsvSeed B k, (M' (bnsvGen hB1 k ω) : Measure (Fin (bnsvS B k))).real
        {z | IsInterior (bnsvGen hB1 k ω) z} := by
    calc (Fintype.card (bnsvSeed B k) : ℝ) * (2 / 3)
        = ∑ _ω : bnsvSeed B k, (2 / 3 : ℝ) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ ∑ ω : bnsvSeed B k, (M' (bnsvGen hB1 k ω) : Measure (Fin (bnsvS B k))).real
            {z | IsInterior (bnsvGen hB1 k ω) z} :=
          Finset.sum_le_sum fun ω _ => hpt_lb ω
  have havg_lb : (2 / 3 : ℝ) ≤
      ((Fintype.card (bnsvSeed B k) : ℝ)⁻¹) *
        ∑ ω : bnsvSeed B k, (M' (bnsvGen hB1 k ω) : Measure (Fin (bnsvS B k))).real
          {z | IsInterior (bnsvGen hB1 k ω) z} := by
    calc (2 / 3 : ℝ)
        = ((Fintype.card (bnsvSeed B k) : ℝ)⁻¹) * ((Fintype.card (bnsvSeed B k) : ℝ) * (2 / 3)) := by
          field_simp [hcard_ne]
      _ ≤ _ := mul_le_mul_of_nonneg_left hsum_lb (inv_nonneg.mpr hcard_pos.le)
  -- Numerical contradiction: `(k + 1) * (exp 1 / (100 * m) + δ) = exp 1 / 100 + m * δ < 3/100 + 1/10 < 2/3`!
  have hexp_lt3 : Real.exp 1 < 3 := by
    have := Real.exp_one_lt_d9
    linarith
  have hm_pos : (0 : ℝ) < (m : ℝ) := by positivity
  have hm_ne : (m : ℝ) ≠ 0 := hm_pos.ne'
  have hB_r : (B : ℝ) = 100 * (m : ℝ) := by dsimp [B]; push_cast; ring
  have hnum : ((k + 1 : ℕ) : ℝ) * (Real.exp 1 / (B : ℝ) + δ) < 2 / 3 := by
    rw [hk_succ, hB_r]
    have hcalc : (m : ℝ) * (Real.exp 1 / (100 * (m : ℝ)) + δ) =
        Real.exp 1 / 100 + (m : ℝ) * δ := by field_simp [hm_ne]
    rw [hcalc]
    linarith
  linarith

end InteriorPointLowerBound


/-! ### Part 5: Lower Bound (`PrivatelyUniformlyGeneratable C → closureDim C < ⊤ ∧ nbDim C ⊤ < ⊤`) -/

section LowerBound

lemma measureReal_eq_zero_of_ae_not {Y : Type*} [MeasurableSpace Y]
    (μ : ProbabilityMeasure Y) {E : Set Y} (hae : ∀ᵐ y ∂(μ : Measure Y), y ∉ E) :
    (μ : Measure Y).real E = 0 := by
  have hsub : E ⊆ {y : Y | ¬ (y ∉ E)} := fun _ hy hnot => hnot hy
  have h0 : (μ : Measure Y) E = 0 := measure_mono_null hsub (ae_iff.mp hae)
  simp [Measure.real, h0]

lemma measureReal_eq_one_of_ae {Y : Type*} [MeasurableSpace Y]
    (μ : ProbabilityMeasure Y) {E : Set Y} (hE : MeasurableSet E)
    (hae : ∀ᵐ y ∂(μ : Measure Y), y ∈ E) :
    (μ : Measure Y).real E = 1 := by
  have hc : (μ : Measure Y) Eᶜ = 0 := ae_iff.mp hae
  have h1 : (μ : Measure Y) E + (μ : Measure Y) Eᶜ = 1 := by
    rw [measure_add_measure_compl hE, measure_univ]
  rw [hc, add_zero] at h1
  simp [Measure.real, h1]

lemma measurable_subset_boolVec {X : Type} [Countable X] {N : ℕ} (K : Fin N → Set X) :
    Measurable (fun Z : Set X => fun i : Fin N => decide (Z ⊆ K i)) := by
  refine measurable_pi_iff.mpr fun i => ?_
  intro s _
  have hsub := measurableSet_subset (K i)
  by_cases ht : true ∈ s <;> by_cases hf : false ∈ s
  · have h : (fun Z : Set X => decide (Z ⊆ K i)) ⁻¹' s = Set.univ := by
      ext Z; simp only [Set.mem_preimage, Set.mem_univ, iff_true]
      cases decide (Z ⊆ K i) <;> assumption
    rw [h]; exact MeasurableSet.univ
  · have h : (fun Z : Set X => decide (Z ⊆ K i)) ⁻¹' s = {Z : Set X | Z ⊆ K i} := by
      ext Z; simp only [Set.mem_preimage]
      by_cases hZ : Z ⊆ K i <;> simp [hZ, ht, hf]
    rw [h]; exact hsub
  · have h : (fun Z : Set X => decide (Z ⊆ K i)) ⁻¹' s = {Z : Set X | Z ⊆ K i}ᶜ := by
      ext Z; simp only [Set.mem_preimage, Set.mem_compl_iff]
      by_cases hZ : Z ⊆ K i <;> simp [hZ, ht, hf]
    rw [h]; exact hsub.compl
  · have h : (fun Z : Set X => decide (Z ⊆ K i)) ⁻¹' s = ∅ := by
      ext Z; simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
      cases decide (Z ⊆ K i) <;> assumption
    rw [h]; exact MeasurableSet.empty

/-- Lemma 6.2: Almost-sure infinite containment in `closure C (support S)` (and any `K ∈ infiniteClosure C`
    containing `S`). -/
lemma ae_subset_closure {X : Type} [Countable X] {C : LanguageClass X} {n : ℕ}
    {A : Mechanism X (Set X) n} (hgen : IsUniformGenerator C A)
    {S : Fin n → X} (hinj : Function.Injective S)
    (hreal : ∃ L ∈ C.languages, ∀ i, S i ∈ L) :
    ∀ᵐ Z ∂(A S : Measure (Set X)), Z.Infinite ∧ Z ⊆ closure C (↑(support S) : Set X) := by
  obtain ⟨L₀, hL₀, hSL₀⟩ := hreal
  have hae₀ := hgen L₀ hL₀ S hSL₀ hinj
  have hae_outside : ∀ x ∈ (closure C (↑(support S) : Set X))ᶜ,
      ∀ᵐ Z ∂(A S : Measure (Set X)), x ∉ Z := by
    intro x hx
    have hnot_all : ¬ (∀ L ∈ C.languages, (↑(support S) : Set X) ⊆ L → x ∈ L) := by
      intro hall
      exact hx (Set.mem_sInter.mpr fun L ⟨hL, hsub⟩ => hall L hL hsub)
    push_neg at hnot_all
    obtain ⟨Lx, hLx, hSLx, hxLx⟩ := hnot_all
    have hSLx_pt : ∀ i, S i ∈ Lx := fun i =>
      hSLx (Finset.mem_coe.mpr (by unfold support; exact Finset.mem_image_of_mem S (Finset.mem_univ i)))
    filter_upwards [hgen Lx hLx S hSLx_pt hinj] with Z hZ hxZ
    exact hxLx (hZ.2 hxZ).1
  have hae_ball := (ae_ball_iff (Set.to_countable _)).mpr hae_outside
  filter_upwards [hae₀, hae_ball] with Z hZ₀ hZsub
  refine ⟨hZ₀.1, fun x hxZ => ?_⟩
  by_contra hxC
  exact hZsub x hxC hxZ

lemma ae_subset_of_mem_infiniteClosure {X : Type} [Countable X] {C : LanguageClass X} {n : ℕ}
    {A : Mechanism X (Set X) n} (hgen : IsUniformGenerator C A)
    {K : Set X} (hK : K ∈ infiniteClosure C) {S : Fin n → X}
    (hinj : Function.Injective S) (hSK : ∀ i, S i ∈ K) :
    ∀ᵐ Z ∂(A S : Measure (Set X)), Z.Infinite ∧ Z ⊆ K := by
  obtain ⟨_, F, ⟨L₀, hL₀F⟩, hFC, hKeq⟩ := id hK
  have hSL₀ : ∀ i, S i ∈ L₀ := fun i => (hKeq ▸ hSK i) L₀ hL₀F
  have hsupp_K : (↑(support S) : Set X) ⊆ K := by
    intro x hx
    unfold support at hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact hSK i
  have hcl_K : closure C (↑(support S) : Set X) ⊆ K :=
    closure_subset_of_mem_infiniteClosure C hK hsupp_K
  filter_upwards [ae_subset_closure hgen hinj ⟨L₀, hFC hL₀F, hSL₀⟩] with Z ⟨hZinf, hZsub⟩
  exact ⟨hZinf, hZsub.trans hcl_K⟩

/-- Lemma 6.3: Non-private uniform generation implies `closureDim C < ⊤`. -/
lemma lower_closureDim_lt_top {X : Type} [Countable X] {C : LanguageClass X} {n : ℕ}
    {A : Mechanism X (Set X) n} (hgen : IsUniformGenerator C A) :
    closureDim C < ⊤ := by
  rw [closureDim_lt_top_iff]
  refine lt_of_le_of_lt (b := (n : ℕ∞)) ?_ (ENat.natCast_lt_top n)
  unfold closureSizeSup
  refine iSup₂_le fun T _ => iSup₂_le fun hreal hfin => ?_
  by_contra hnot
  have hge : n ≤ T.card := by
    have hlt : (n : ℕ∞) < (T.card : ℕ∞) := lt_of_not_ge hnot
    exact (Nat.cast_lt.mp hlt).le
  obtain ⟨T₀, hT₀_sub, hT₀_card⟩ := Finset.exists_subset_card_eq hge
  let e : Fin n ≃ T₀ := (T₀.equivFinOfCardEq hT₀_card).symm
  let S : Fin n → X := fun i => (e i).val
  have hinj : Function.Injective S := fun i₁ i₂ heq => e.injective (Subtype.ext heq)
  obtain ⟨L, hL, hTL⟩ := hreal
  have hSL : ∀ i, S i ∈ L := fun i => hTL (Finset.mem_coe.mpr (hT₀_sub (e i).2))
  have hae := ae_subset_closure hgen hinj ⟨L, hL, hSL⟩
  have hmeas_E : MeasurableSet {Z : Set X | Z.Infinite ∧ Z ⊆ closure C (↑(support S) : Set X)} :=
    measurableSet_infinite.inter (measurableSet_subset _)
  have hprob1 := measureReal_eq_one_of_ae (A S) hmeas_E hae
  have hne : {Z : Set X | Z.Infinite ∧ Z ⊆ closure C (↑(support S) : Set X)}.Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty.mp hemp, measureReal_empty] at hprob1
    norm_num at hprob1
  obtain ⟨Z, hZinf, hZsub⟩ := hne
  have hsupp_T : (↑(support S) : Set X) ⊆ (↑T : Set X) := by
    intro x hx
    unfold support at hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_coe.mpr (hT₀_sub (e i).2)
  exact hZinf (hfin.subset (hZsub.trans (closure_mono C hsupp_T)))

/-- State at stage `k` of the recursive sequence `B_0 ⊇ ... ⊇ B_k` in Lemma 6.5 Case 2. -/
structure HellyChain {X : Type} (C : LanguageClass X) (F : Set (Set X))
    (n : ℕ) (A : Mechanism X (Set X) n) (k : ℕ) where
  G : Fin (k + 1) → Finset (Set X)
  hG_ne : ∀ j : Fin (k + 1), (G j).Nonempty
  hG_sub : ∀ j : Fin (k + 1), (↑(G j) : Set (Set X)) ⊆ F
  hG_mono : ∀ {j₁ j₂ : Fin (k + 1)}, j₁ ≤ j₂ → G j₁ ⊆ G j₂
  pts : Fin k → Fin n → X
  pts_inj : Function.Injective (fun p : Fin k × Fin n => pts p.1 p.2)
  pts_mem : ∀ (i : Fin k) (t : Fin n), pts i t ∈ ⋂₀ (↑(G i.castSucc) : Set (Set X))
  fail_prob : ∀ (i : Fin k) (y : Fin n → Fin (i.val + 1)),
    2 / 3 ≤ (A (fun t => pts ⟨(y t).val, by omega⟩ t) : Measure (Set X)).real
      {Z : Set X | ¬ (Z ⊆ ⋂₀ (↑(G i.succ) : Set (Set X)))}

/-- Lemma 6.5: `(1, δ')`-DP uniform generation with `n * δ' ≤ 1/10` implies `n`-Helly on `infiniteClosure C`. -/
lemma lower_helly_infiniteClosure {X : Type} [Countable X] {C : LanguageClass X}
    {n : ℕ} (hn : 2 ≤ n) {δ' : ℝ} (hδ0 : 0 ≤ δ') (hδ : (n : ℝ) * δ' ≤ 1 / 10)
    {A : Mechanism X (Set X) n} (hdp : IsDP A 1 δ') (hgen : IsUniformGenerator C A)
    {F : Set (Set X)} (hne : F.Nonempty) (hF : F ⊆ infiniteClosure C) (hfin : (⋂₀ F).Finite) :
    ∃ G : Finset (Set X), G.Nonempty ∧ (↑G : Set (Set X)) ⊆ F ∧
      G.card ≤ n ∧ (⋂₀ (↑G : Set (Set X))).Finite := by
  by_contra hno
  have hno_le_n : ∀ G : Finset (Set X), G.Nonempty → (↑G : Set (Set X)) ⊆ F →
      G.card ≤ n → (⋂₀ (↑G : Set (Set X))).Infinite := by
    intro G hGne hGF hGc
    by_contra hnotinf
    exact hno ⟨G, hGne, hGF, hGc, Set.not_infinite.mp hnotinf⟩
  by_cases hfin_sub : ∃ G : Finset (Set X), G.Nonempty ∧ (↑G : Set (Set X)) ⊆ F ∧
      (⋂₀ (↑G : Set (Set X))).Finite
  · -- Case 1: Some finite subfamily of `F` has finite intersection. Pick one of minimum cardinality `r ≥ n + 1`.
    have hex_r : ∃ r : ℕ, ∃ G : Finset (Set X), G.card = r ∧ G.Nonempty ∧
        (↑G : Set (Set X)) ⊆ F ∧ (⋂₀ (↑G : Set (Set X))).Finite := by
      obtain ⟨G, h1, h2, h3⟩ := hfin_sub
      exact ⟨G.card, G, rfl, h1, h2, h3⟩
    set r := Nat.find hex_r
    obtain ⟨G, hGcard, hGne, hGF, hGfin⟩ := Nat.find_spec hex_r
    have hr_gt_n : n + 1 ≤ r := by
      by_contra hle
      exact (hno_le_n G hGne hGF (by omega)) hGfin
    let eG : Fin r ≃ G := (G.equivFinOfCardEq hGcard).symm
    let K : Fin r → Set X := fun j => (eG j).val
    have hK_ic : ∀ j : Fin r, K j ∈ infiniteClosure C := fun j => hF (hGF (eG j).2)
    have hInter_eq : (⋂ j : Fin r, K j) = ⋂₀ (↑G : Set (Set X)) := by
      ext x
      simp only [Set.mem_iInter, Set.mem_sInter, Finset.mem_coe]
      exact ⟨fun hx A hAG => by
        have : eG (eG.symm ⟨A, hAG⟩) = ⟨A, hAG⟩ := eG.apply_symm_apply _
        have hKeq : K (eG.symm ⟨A, hAG⟩) = A := congrArg Subtype.val this
        exact hKeq ▸ hx (eG.symm ⟨A, hAG⟩),
        fun hx j => hx (K j) (eG j).2⟩
    have hInter_fin : (⋂ j : Fin r, K j).Finite := hInter_eq ▸ hGfin
    -- Omitting any single `j : Fin r` leaves an infinite intersection by minimality of `r`!
    have homit_inf : ∀ j : Fin r, (⋂ (j' : Fin r) (_ : j' ≠ j), K j').Infinite := by
      intro j
      set G' : Finset (Set X) := G.erase (K j)
      have hKj_mem : K j ∈ G := (eG j).2
      have hG'_card : G'.card = r - 1 := by
        have h1 : G'.card + 1 = G.card := Finset.card_erase_add_one hKj_mem
        omega
      have hG'_ne : G'.Nonempty := Finset.card_pos.mp (by omega)
      have hG'_sub : (↑G' : Set (Set X)) ⊆ F :=
        (Finset.coe_subset.mpr (Finset.erase_subset _ _)).trans hGF
      have hnot_fin : ¬ (⋂₀ (↑G' : Set (Set X))).Finite := fun hf =>
        Nat.find_min hex_r (m := r - 1) (by omega) ⟨G', hG'_card, hG'_ne, hG'_sub, hf⟩
      have hG'_inf : (⋂₀ (↑G' : Set (Set X))).Infinite := Set.not_infinite.mp.mt hnot_fin |> not_not.mp
      have heq_omit : ⋂₀ (↑G' : Set (Set X)) = ⋂ (j' : Fin r) (_ : j' ≠ j), K j' := by
        ext x
        simp only [G', Set.mem_sInter, Finset.mem_coe, Finset.mem_erase, Set.mem_iInter]
        constructor
        · intro hx j' hj'
          have hne_val : K j' ≠ K j := fun heq => hj' (eG.injective (Subtype.ext heq))
          exact hx (K j') ⟨hne_val, (eG j').2⟩
        · intro hx A ⟨hAne, hAG⟩
          let idx := eG.symm ⟨A, hAG⟩
          have hKidx : K idx = A := congrArg Subtype.val (eG.apply_symm_apply ⟨A, hAG⟩)
          have hidx_ne : idx ≠ j := fun heq => hAne (hKidx ▸ congrArg K heq)
          exact hKidx ▸ hx idx hidx_ne
      exact heq_omit ▸ hG'_inf
    let P : Fin r → Set X := fun j => (⋂ (j' : Fin r) (_ : j' ≠ j), K j') \ (⋂ j' : Fin r, K j')
    have hP_inf : ∀ j : Fin r, (P j).Infinite := fun j => (homit_inf j).sdiff hInter_fin
    have hP_disj : ∀ {j₁ j₂ : Fin r}, j₁ ≠ j₂ → Disjoint (P j₁) (P j₂) := by
      intro j₁ j₂ hne
      rw [Set.disjoint_left]
      intro x hx1 hx2
      have hx_not_j1 : x ∉ K j₁ := by
        intro hxj1
        apply hx1.2
        rw [Set.mem_iInter]
        intro j'
        by_cases hj' : j' = j₁
        · subst hj'; exact hxj1
        · exact (Set.mem_iInter₂.mp hx1.1) j' hj'
      exact hx_not_j1 ((Set.mem_iInter₂.mp hx2.1) j₁ hne)
    let mr := r - 1
    let emb : Fin mr → Fin r := fun i => ⟨i.val, by omega⟩
    let last : Fin r := ⟨r - 1, by omega⟩
    let aPt : Fin mr → Fin n → X := fun i t => ((enumInfSet _ (hP_inf (emb i))) t.val).val
    have haPt_mem : ∀ i t, aPt i t ∈ P (emb i) := fun i t => ((enumInfSet _ (hP_inf (emb i))) t.val).2
    let encS : (Fin n → Fin mr) → (Fin n → X) := fun y t => aPt (y t) t
    have henc_inj : ∀ y : Fin n → Fin mr, Function.Injective (encS y) := by
      intro y t₁ t₂ heq
      by_cases hy : y t₁ = y t₂
      · dsimp only [encS, aPt] at heq
        rw [hy] at heq
        have hsub := (enumInfSet _ (hP_inf (emb (y t₂)))).injective (Subtype.ext heq)
        exact Fin.ext hsub
      · have hne_emb : emb (y t₁) ≠ emb (y t₂) := fun h =>
          hy (Fin.ext (by
            have hv := congrArg Fin.val h
            dsimp [emb] at hv
            exact hv))
        exfalso
        have hmem1 : aPt (y t₂) t₂ ∈ P (emb (y t₁)) := by
          dsimp only [encS] at heq
          rw [← heq]
          exact haPt_mem (y t₁) t₁
        exact Set.disjoint_left.mp (hP_disj hne_emb) hmem1 (haPt_mem (y t₂) t₂)
    have henc_in_last : ∀ (y : Fin n → Fin mr) (t : Fin n), encS y t ∈ K last := by
      intro y t
      have hne_last : last ≠ emb (y t) := by
        intro heq
        have hv : r - 1 = (y t).val := congrArg Fin.val heq
        have := (y t).isLt
        omega
      exact (Set.mem_iInter₂.mp (haPt_mem (y t) t).1) last hne_last
    -- Consider `y₀ t = ⟨t.val, _⟩` and replacement neighbors `y_alt s` replacing coordinate `s`!
    let y₀ : Fin n → Fin mr := fun t => ⟨t.val, by omega⟩
    let E_bad : Fin n → Set (Set X) := fun t => {Z : Set X | ¬ (Z ⊆ K (emb ⟨t.val, by omega⟩))}
    have hE_meas : ∀ t : Fin n, MeasurableSet (E_bad t) := fun t => (measurableSet_subset _).compl
    -- On `y₀`, almost surely `Z ∈ ⋃ t : Fin n, E_bad t`!
    have hae_union_y0 : ∀ᵐ Z ∂(A (encS y₀) : Measure (Set X)), Z ∈ ⋃ t : Fin n, E_bad t := by
      have hae_last := ae_subset_of_mem_infiniteClosure hgen (hK_ic last) (henc_inj y₀) (henc_in_last y₀)
      have hae_other : ∀ i : Fin mr, n ≤ i.val →
          ∀ᵐ Z ∂(A (encS y₀) : Measure (Set X)), Z ⊆ K (emb i) := by
        intro i hi_ge
        have h_in_Ki : ∀ t : Fin n, encS y₀ t ∈ K (emb i) := by
          intro t
          have hne_i : emb i ≠ emb (y₀ t) := by
            intro heq
            have hv : i.val = t.val := congrArg Fin.val heq
            omega
          exact (Set.mem_iInter₂.mp (haPt_mem (y₀ t) t).1) (emb i) hne_i
        filter_upwards [ae_subset_of_mem_infiniteClosure hgen (hK_ic (emb i)) (henc_inj y₀) h_in_Ki]
          with Z hZ using hZ.2
      have hae_all_other : ∀ᵐ Z ∂(A (encS y₀) : Measure (Set X)),
          ∀ i : Fin mr, n ≤ i.val → Z ⊆ K (emb i) := by
        refine (ae_all_iff.mpr fun i => ?_)
        by_cases hi : n ≤ i.val
        · filter_upwards [hae_other i hi] with Z hZ _ using hZ
        · exact Filter.Eventually.of_forall fun _ h => absurd h hi
      filter_upwards [hae_last, hae_all_other] with Z ⟨hZinf, hZlast⟩ hZother
      rw [Set.mem_iUnion]
      by_contra hnone
      push_neg at hnone
      have hZ_sub_all : Z ⊆ ⋂ j : Fin r, K j := by
        rw [Set.subset_iInter_iff]
        intro j
        by_cases hj_last : j.val = r - 1
        · have : j = last := Fin.ext hj_last
          subst this; exact hZlast
        · let i : Fin mr := ⟨j.val, by dsimp [mr]; have := j.isLt; omega⟩
          have hij : emb i = j := Fin.ext rfl
          rw [← hij]
          by_cases hjn : j.val < n
          · have hnotE : Z ∉ E_bad ⟨j.val, hjn⟩ := hnone ⟨j.val, hjn⟩
            simpa [E_bad, i] using hnotE
          · exact hZother i (Nat.le_of_not_lt hjn)
      exact hZinf (hInter_fin.subset hZ_sub_all)
    have hprob1_union : (A (encS y₀) : Measure (Set X)).real (⋃ t : Fin n, E_bad t) = 1 :=
      measureReal_eq_one_of_ae (A (encS y₀)) (MeasurableSet.iUnion hE_meas) hae_union_y0
    have hsum_ge1 : (1 : ℝ) ≤ ∑ t : Fin n, (A (encS y₀) : Measure (Set X)).real (E_bad t) := by
      have hunion_eq : (⋃ t : Fin n, E_bad t) = ⋃ t ∈ (Finset.univ : Finset (Fin n)), E_bad t := by
        simp
      rw [← hprob1_union, hunion_eq]
      exact measureReal_biUnion_finset_le Finset.univ E_bad
    -- Each term `(A (encS y₀)).real (E_bad t) ≤ δ'` by DP against `y_alt t`!
    have hterm_le_δ : ∀ t : Fin n, (A (encS y₀) : Measure (Set X)).real (E_bad t) ≤ δ' := by
      intro t
      let alt_val : Fin mr := ⟨(t.val + 1) % n, by dsimp [mr]; have := Nat.mod_lt (t.val + 1) (by omega : 0 < n); omega⟩
      let y_alt : Fin n → Fin mr := Function.update y₀ t alt_val
      have hnear_alt : Near (encS y₀) (encS y_alt) :=
        near_of_eq_except t fun s hs => by simp [encS, y_alt, hs]
      have hzero_alt : (A (encS y_alt) : Measure (Set X)).real (E_bad t) = 0 := by
        have h_in_Kt : ∀ s : Fin n, encS y_alt s ∈ K (emb ⟨t.val, by dsimp [mr]; have := t.isLt; omega⟩) := by
          intro s
          have hne_t : emb ⟨t.val, by dsimp [mr]; have := t.isLt; omega⟩ ≠ emb (y_alt s) := by
            intro heq
            have hv : t.val = (y_alt s).val := congrArg Fin.val heq
            by_cases hst : s = t
            · rw [hst] at hv
              simp only [y_alt, Function.update_self, alt_val] at hv
              have ht_lt : t.val < n := t.isLt
              by_cases ht1 : t.val + 1 < n
              · rw [Nat.mod_eq_of_lt ht1] at hv; omega
              · have ht_eq : t.val + 1 = n := by omega
                rw [ht_eq, Nat.mod_self] at hv; omega
            · simp only [y_alt, Function.update_of_ne hst, y₀] at hv
              exact hst (Fin.ext hv.symm)
          exact (Set.mem_iInter₂.mp (haPt_mem (y_alt s) s).1) _ hne_t
        have hae_sub := ae_subset_of_mem_infiniteClosure hgen
          (hK_ic (emb ⟨t.val, by dsimp [mr]; have := t.isLt; omega⟩)) (henc_inj y_alt) h_in_Kt
        refine measureReal_eq_zero_of_ae_not (A (encS y_alt)) ?_
        filter_upwards [hae_sub] with Z hZ hZE using hZE hZ.2
      have hdp_step := isDP_near_le hdp (by norm_num) hδ0 hnear_alt (hE_meas t)
      rw [hzero_alt, mul_zero, zero_add] at hdp_step
      exact hdp_step
    have hsum_le_nδ : ∑ t : Fin n, (A (encS y₀) : Measure (Set X)).real (E_bad t) ≤ (n : ℝ) * δ' := by
      calc ∑ t : Fin n, (A (encS y₀) : Measure (Set X)).real (E_bad t)
          ≤ ∑ _t : Fin n, δ' := Finset.sum_le_sum fun t _ => hterm_le_δ t
        _ = (n : ℝ) * δ' := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    linarith
  · -- Case 2: Every nonempty finite subfamily of `F` has infinite intersection!
    have hall_inf : ∀ G : Finset (Set X), G.Nonempty → (↑G : Set (Set X)) ⊆ F →
        (⋂₀ (↑G : Set (Set X))).Infinite := by
      intro G hGne hGF
      by_contra hnotinf
      exact hfin_sub ⟨G, hGne, hGF, Set.not_infinite.mp hnotinf⟩
    have : Infinite X := infinite_X_of_languageClass C
    let enumX : ℕ ≃ X := Classical.choice (nonempty_equiv_of_countable (α := ℕ) (β := X))
    let W : ℕ → Finset X := fun q => ((Finset.range q).image enumX).filter (· ∉ ⋂₀ F)
    let Hit : ℕ → Set (Set X) := fun q => ⋃ x ∈ W q, {Z : Set X | x ∈ Z}
    have hHit_meas : ∀ q : ℕ, MeasurableSet (Hit q) := fun q =>
      MeasurableSet.biUnion (Finset.countable_toSet (W q)) fun x _ => measurableSet_mem x
    have hHit_mono : Monotone Hit := by
      intro q₁ q₂ hle Z hZ
      simp only [Hit, Set.mem_iUnion] at hZ ⊢
      obtain ⟨x, hxW, hxZ⟩ := hZ
      refine ⟨x, ?_, hxZ⟩
      simp only [W, Finset.mem_filter, Finset.mem_image, Finset.mem_range] at hxW ⊢
      obtain ⟨⟨m, hm, rfl⟩, hxF⟩ := hxW
      exact ⟨⟨m, lt_of_lt_of_le hm hle, rfl⟩, hxF⟩
    -- Helper: for any single `S` where `A S` is a.s. infinite, `∃ q, 2/3 ≤ (A S).real (Hit q)`!
    have hex_q_single : ∀ S : Fin n → X,
        (∀ᵐ Z ∂(A S : Measure (Set X)), Z.Infinite) →
        ∃ q : ℕ, 2 / 3 ≤ (A S : Measure (Set X)).real (Hit q) := by
      intro S hae_inf
      have hae_hit : ∀ᵐ Z ∂(A S : Measure (Set X)), Z ∈ ⋃ q : ℕ, Hit q := by
        filter_upwards [hae_inf] with Z hZinf
        have hdiff_ne : (Z \ ⋂₀ F).Nonempty := (hZinf.sdiff hfin).nonempty
        obtain ⟨x, hxZ, hxF⟩ := hdiff_ne
        let m := enumX.symm x
        refine Set.mem_iUnion.mpr ⟨m + 1, Set.mem_iUnion₂.mpr ⟨x, ?_, hxZ⟩⟩
        simp only [W, Finset.mem_filter, Finset.mem_image, Finset.mem_range]
        exact ⟨⟨m, Nat.lt_succ_self m, enumX.apply_symm_apply x⟩, hxF⟩
      have hmeas_u : MeasurableSet (⋃ q : ℕ, Hit q) := MeasurableSet.iUnion hHit_meas
      have hu_one : (A S : Measure (Set X)) (⋃ q : ℕ, Hit q) = 1 := by
        have hr := measureReal_eq_one_of_ae (A S) hmeas_u hae_hit
        have hne_top : (A S : Measure (Set X)) (⋃ q : ℕ, Hit q) ≠ ⊤ := measure_ne_top _ _
        exact (ENNReal.toReal_eq_one_iff _).mp hr
      have htend_enn := tendsto_measure_iUnion_atTop hHit_mono (μ := (A S : Measure (Set X)))
      rw [hu_one] at htend_enn
      have htend_real : Tendsto (fun q => (A S : Measure (Set X)).real (Hit q)) atTop (nhds 1) := by
        have h := (ENNReal.continuousAt_toReal ENNReal.one_ne_top).tendsto.comp htend_enn
        exact h.congr fun _ => rfl
      obtain ⟨q₀, hq₀⟩ := Metric.tendsto_atTop.mp htend_real (1 / 3) (by norm_num)
      refine ⟨q₀, ?_⟩
      have hd := hq₀ q₀ (le_refl q₀)
      rw [Real.dist_eq] at hd
      have := abs_lt.mp hd
      linarith
    -- Construct `HellyChain C F n A k` for all `k : ℕ` by recursion!
    obtain ⟨B₀, hB₀F⟩ := hne
    have hchain : ∀ k : ℕ, Nonempty (HellyChain C F n A k) := by
      intro k
      induction k with
      | zero =>
          refine ⟨{
            G := fun _ => {B₀}
            hG_ne := fun _ => Finset.singleton_nonempty B₀
            hG_sub := fun _ => by simp [hB₀F]
            hG_mono := fun _ => Finset.Subset.refl _
            pts := fun i => i.elim0
            pts_inj := fun p₁ _ _ => p₁.1.elim0
            pts_mem := fun i => i.elim0
            fail_prob := fun i => i.elim0
          }⟩
      | succ k ih =>
          obtain ⟨ch⟩ := ih
          -- Pick `n` fresh points from `⋂₀ ↑(ch.G (Fin.last k)) \ (⋂₀ F ∪ used)`!
          let B_last : Set X := ⋂₀ (↑(ch.G (Fin.last k)) : Set (Set X))
          have hBlast_inf : B_last.Infinite :=
            hall_inf (ch.G (Fin.last k)) (ch.hG_ne _) (ch.hG_sub _)
          let used : Set X := Set.range fun p : Fin k × Fin n => ch.pts p.1 p.2
          have hrem_inf : (B_last \ (⋂₀ F ∪ used)).Infinite :=
            hBlast_inf.sdiff (hfin.union (Set.finite_range _))
          let new_pts : Fin n → X := fun t => ((enumInfSet _ hrem_inf) t.val).val
          have hnew_mem : ∀ t : Fin n, new_pts t ∈ B_last \ (⋂₀ F ∪ used) := fun t =>
            ((enumInfSet _ hrem_inf) t.val).2
          let pts' : Fin (k + 1) → Fin n → X := fun i t =>
            if hi : i.val < k then ch.pts ⟨i.val, hi⟩ t else new_pts t
          have hpts'_old : ∀ (i : Fin k) (t : Fin n), pts' i.castSucc t = ch.pts i t := by
            intro i t; simp [pts', i.isLt]
          have hpts'_last : ∀ t : Fin n, pts' (Fin.last k) t = new_pts t := by
            intro t; simp [pts']
          have hpts'_inj : Function.Injective (fun p : Fin (k + 1) × Fin n => pts' p.1 p.2) := by
            rintro ⟨i₁, t₁⟩ ⟨i₂, t₂⟩ heq
            dsimp only [pts'] at heq
            by_cases hi₁ : i₁.val < k <;> by_cases hi₂ : i₂.val < k <;>
              simp only [hi₁, hi₂, ↓reduceDIte] at heq
            · have hp := @ch.pts_inj (⟨i₁.val, hi₁⟩, t₁) (⟨i₂.val, hi₂⟩, t₂) heq
              injection hp with h1 h2
              have hv : i₁.val = i₂.val := congrArg (Fin.val : Fin k → ℕ) h1
              exact Prod.ext (Fin.ext hv) h2
            · exfalso
              exact (hnew_mem t₂).2 (Or.inr ⟨(⟨i₁.val, hi₁⟩, t₁), heq⟩)
            · exfalso
              exact (hnew_mem t₁).2 (Or.inr ⟨(⟨i₂.val, hi₂⟩, t₂), heq.symm⟩)
            · have hi_eq : i₁ = i₂ := Fin.ext (by have := i₁.isLt; have := i₂.isLt; omega)
              have ht_eq : t₁ = t₂ := Fin.ext ((enumInfSet _ hrem_inf).injective (Subtype.ext heq))
              exact Prod.ext hi_eq ht_eq
          -- Every `pts' i t ∈ B_0 := ⋂₀ ↑(ch.G 0)`!
          have hB0_ic : ⋂₀ (↑(ch.G 0) : Set (Set X)) ∈ infiniteClosure C :=
            sInter_mem_infiniteClosure C (Finset.coe_nonempty.mpr (ch.hG_ne 0))
              ((ch.hG_sub 0).trans hF) (hall_inf (ch.G 0) (ch.hG_ne 0) (ch.hG_sub 0))
          have hpts'_in_B0 : ∀ (i : Fin (k + 1)) (t : Fin n),
              pts' i t ∈ ⋂₀ (↑(ch.G 0) : Set (Set X)) := by
            intro i t
            dsimp only [pts']
            split_ifs with hi
            · have hm := ch.pts_mem ⟨i.val, hi⟩ t
              have hsubG : ch.G 0 ⊆ ch.G (⟨i.val, hi⟩ : Fin k).castSucc := ch.hG_mono (Fin.zero_le _)
              exact Set.sInter_subset_sInter (Finset.coe_subset.mpr hsubG) hm
            · have hm := (hnew_mem t).1
              have hsubG : ch.G 0 ⊆ ch.G (Fin.last k) := ch.hG_mono (Fin.zero_le _)
              exact Set.sInter_subset_sInter (Finset.coe_subset.mpr hsubG) hm
          -- Uniformly choose `q_k : ℕ` across all `y : Fin n → Fin (k + 1)`!
          let enc_k : (Fin n → Fin (k + 1)) → (Fin n → X) := fun y t => pts' (y t) t
          have henc_k_inj : ∀ y : Fin n → Fin (k + 1), Function.Injective (enc_k y) :=
            fun y t₁ t₂ heq => (Prod.ext_iff.mp (@hpts'_inj (y t₁, t₁) (y t₂, t₂) heq)).2
          choose q_of hq_of using fun y : Fin n → Fin (k + 1) =>
            hex_q_single (enc_k y) (by
              filter_upwards [ae_subset_of_mem_infiniteClosure hgen hB0_ic (henc_k_inj y)
                (fun t => hpts'_in_B0 (y t) t)] with Z hZ using hZ.1)
          let qk : ℕ := Finset.univ.sup q_of
          -- For each `x ∈ W qk`, pick `Fx x ∈ F` excluding `x`!
          have hex_excl : ∀ x : {x // x ∈ W qk}, ∃ A_set ∈ F, x.val ∉ A_set := by
            intro ⟨x, hxW⟩
            have hx_notF : x ∉ ⋂₀ F := (Finset.mem_filter.mp hxW).2
            by_contra hall_in
            push_neg at hall_in
            exact hx_notF (Set.mem_sInter.mpr hall_in)
          choose excl hexcl_mem hexcl_not using hex_excl
          let G_next : Finset (Set X) := ch.G (Fin.last k) ∪ (W qk).attach.image excl
          have hG_next_sub : (↑G_next : Set (Set X)) ⊆ F := by
            intro A_set hA
            rcases Finset.mem_union.mp (Finset.mem_coe.mp hA) with h1 | h2
            · exact ch.hG_sub (Fin.last k) (Finset.mem_coe.mpr h1)
            · obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp h2
              exact hexcl_mem x
          let G' : Fin (k + 2) → Finset (Set X) := fun j =>
            if hj : j.val ≤ k then ch.G ⟨j.val, by omega⟩ else G_next
          have hG'_old : ∀ j : Fin (k + 1), G' j.castSucc = ch.G j := by
            intro j
            have hj_le : j.val ≤ k := by omega
            simp [G', hj_le]
          have hG'_last : G' (Fin.last (k + 1)) = G_next := by
            simp [G']
          refine ⟨{
            G := G'
            hG_ne := fun j => by
              dsimp only [G']
              split_ifs with hj
              · exact ch.hG_ne ⟨j.val, by omega⟩
              · exact (ch.hG_ne (Fin.last k)).mono Finset.subset_union_left
            hG_sub := fun j => by
              dsimp only [G']
              split_ifs with hj
              · exact ch.hG_sub ⟨j.val, by omega⟩
              · exact hG_next_sub
            hG_mono := fun {j₁ j₂} hle => by
              have hv : j₁.val ≤ j₂.val := Fin.le_iff_val_le_val.mp hle
              dsimp only [G']
              split_ifs with h1 h2
              · exact ch.hG_mono (Fin.le_iff_val_le_val.mpr hv)
              · exact (ch.hG_mono (j₂ := Fin.last k) (Fin.le_iff_val_le_val.mpr h1)).trans
                  Finset.subset_union_left
              · omega
              · exact Finset.Subset.refl _
            pts := pts'
            pts_inj := hpts'_inj
            pts_mem := fun i t => by
              rw [hG'_old i]
              by_cases hi : i.val < k
              · have hic : i = (⟨i.val, hi⟩ : Fin k).castSucc := Fin.ext rfl
                rw [hic, hpts'_old]
                exact ch.pts_mem ⟨i.val, hi⟩ t
              · have hil : i = Fin.last k := Fin.ext (by have := i.isLt; simp [Fin.last]; omega)
                rw [hil, hpts'_last]
                exact (hnew_mem t).1
            fail_prob := fun i y => by
              by_cases hi : i.val < k
              · let i₀ : Fin k := ⟨i.val, hi⟩
                have hisucc : i.succ = i₀.succ.castSucc := Fin.ext rfl
                rw [hisucc, hG'_old]
                have henc_eq : (fun t => pts' ⟨(y t).val, by omega⟩ t) =
                    (fun t => ch.pts ⟨(y t).val, by omega⟩ t) := by
                  ext t
                  have hyt : (y t).val < k := lt_of_lt_of_le (y t).isLt (by omega)
                  simp [pts', hyt]
                rw [henc_eq]
                exact ch.fail_prob i₀ y
              · have hil : i = Fin.last k := Fin.ext (by have := i.isLt; simp [Fin.last]; omega)
                have hisucc : i.succ = Fin.last (k + 1) := Fin.ext (by simp [hil])
                rw [hisucc, hG'_last]
                let y' : Fin n → Fin (k + 1) := fun t => ⟨(y t).val, by have := (y t).isLt; omega⟩
                have henc_eq : (fun t => pts' ⟨(y t).val, by omega⟩ t) = enc_k y' := rfl
                rw [henc_eq]
                have hq_le : q_of y' ≤ qk := Finset.le_sup (Finset.mem_univ y')
                have hsub_ev : Hit (q_of y') ⊆ {Z : Set X | ¬ (Z ⊆ ⋂₀ (↑G_next : Set (Set X)))} := by
                  intro Z hZ hZsub
                  have hZqk : Z ∈ Hit qk := hHit_mono hq_le hZ
                  simp only [Hit, Set.mem_iUnion] at hZqk
                  obtain ⟨x, hxW, hxZ⟩ := hZqk
                  have hexcl_in : excl ⟨x, hxW⟩ ∈ G_next :=
                    Finset.mem_union_right _ (Finset.mem_image_of_mem excl (Finset.mem_attach _ ⟨x, hxW⟩))
                  exact hexcl_not ⟨x, hxW⟩ (hZsub hxZ _ hexcl_in)
                exact (hq_of y').trans (measureReal_mono hsub_ev)
          }⟩
    -- Instantiate `HellyChain` at `N := bnsvS (100 * n) (n - 1)` and get contradiction!
    obtain ⟨hN_ge2, hno_mech⟩ := no_dp_interior_point (by omega : 1 ≤ n) hδ0 hδ
    set N := bnsvS (100 * n) (n - 1)
    obtain ⟨chN⟩ := hchain N
    let B_set : Fin (N + 1) → Set X := fun j => ⋂₀ (↑(chN.G j) : Set (Set X))
    have hB_anti : ∀ {j₁ j₂ : Fin (N + 1)}, j₁ ≤ j₂ → B_set j₂ ⊆ B_set j₁ := fun hle =>
      Set.sInter_subset_sInter (Finset.coe_subset.mpr (chN.hG_mono hle))
    have hB_ic : ∀ j : Fin (N + 1), B_set j ∈ infiniteClosure C := fun j =>
      sInter_mem_infiniteClosure C (Finset.coe_nonempty.mpr (chN.hG_ne j))
        ((chN.hG_sub j).trans hF) (hall_inf (chN.G j) (chN.hG_ne j) (chN.hG_sub j))
    -- Measurable decoder `dec : Set X → Fin N`: least `i : Fin N` with `¬ (Z ⊆ B_set i.succ)`, else `N - 1`.
    let postBool : (Fin N → Bool) → Fin N := fun bv =>
      if h : (Finset.univ.filter fun i : Fin N => bv i = false).Nonempty then
        (Finset.univ.filter fun i : Fin N => bv i = false).min' h
      else
        ⟨N - 1, by omega⟩
    let dec : Set X → Fin N := postBool ∘ (fun Z i => decide (Z ⊆ B_set i.succ))
    have hdec_meas : Measurable dec :=
      (measurable_of_finite postBool).comp (measurable_subset_boolVec fun i => B_set i.succ)
    let encY : Unit → (Fin n → Fin N) → (Fin n → X) := fun _ y t => chN.pts (y t) t
    have hencY_near : ∀ (u : Unit) {y y' : Fin n → Fin N},
        Neighbors y y' → Near (encY u y) (encY u y') := by
      intro _ y y' ⟨t₀, _, hrest⟩
      exact near_of_eq_except t₀ fun t ht => by simp [encY, hrest t ht]
    let M : Mechanism (Fin N) (Fin N) n := fun y =>
      avgMapPM (fun u : Unit => A (encY u y)) (fun _ => dec) (fun _ => hdec_meas)
    have hM_dp : IsDP M 1 δ' :=
      isDP_avgMap A hdp (by norm_num) hδ0 encY hencY_near (fun _ => dec) (fun _ => hdec_meas)
    apply hno_mech
    refine ⟨M, hM_dp, fun y => ?_⟩
    rw [avgMapPM_real_apply _ _ _ (DiscreteMeasurableSpace.forall_measurableSet _)]
    simp only [Fintype.card_unit, Nat.cast_one, inv_one, one_mul, Finset.univ_unique,
      Finset.sum_singleton]
    have himg_ne : (Finset.univ.image y).Nonempty := by
      exact Finset.image_nonempty.mpr (Finset.univ_nonempty_iff.mpr ⟨⟨0, by omega⟩⟩)
    let ℓ := (Finset.univ.image y).min' himg_ne
    let r_max := (Finset.univ.image y).max' himg_ne
    obtain ⟨t_min, _, ht_min⟩ := Finset.mem_image.mp (Finset.min'_mem _ himg_ne)
    obtain ⟨t_max, _, ht_max⟩ := Finset.mem_image.mp (Finset.max'_mem _ himg_ne)
    have hℓ_le : ∀ t : Fin n, ℓ ≤ y t := fun t =>
      Finset.min'_le _ (y t) (Finset.mem_image_of_mem y (Finset.mem_univ t))
    have hy_le_r : ∀ t : Fin n, y t ≤ r_max := fun t =>
      Finset.le_max' _ (y t) (Finset.mem_image_of_mem y (Finset.mem_univ t))
    -- Almost surely `Z ⊆ B_set ℓ.castSucc`!
    have hinj_Sy : Function.Injective (encY () y) := fun t₁ t₂ heq =>
      (Prod.ext_iff.mp (@chN.pts_inj (y t₁, t₁) (y t₂, t₂) heq)).2
    have hSy_in_Bℓ : ∀ t : Fin n, encY () y t ∈ B_set ℓ.castSucc := fun t =>
      hB_anti (Fin.castSucc_le_castSucc_iff.mpr (hℓ_le t)) (chN.pts_mem (y t) t)
    have hae_Bℓ := ae_subset_of_mem_infiniteClosure hgen (hB_ic ℓ.castSucc) hinj_Sy hSy_in_Bℓ
    -- Also `(A (encY () y)).real {Z | ¬ (Z ⊆ B_set r_max.succ)} ≥ 2 / 3`!
    let y_bd : Fin n → Fin (r_max.val + 1) := fun t =>
      ⟨(y t).val, Nat.lt_succ_of_le (Fin.le_iff_val_le_val.mp (hy_le_r t))⟩
    have hfail_r : 2 / 3 ≤ (A (encY () y) : Measure (Set X)).real
        {Z : Set X | ¬ (Z ⊆ B_set r_max.succ)} := by
      have heq_fn : (fun t => chN.pts ⟨(y_bd t).val, by omega⟩ t) = encY () y := rfl
      simpa [heq_fn, B_set] using chN.fail_prob r_max y_bd
    -- Intersect `{Z | ¬ (Z ⊆ B_set r_max.succ)}` with `{Z | Z ⊆ B_set ℓ.castSucc}` (which has complement measure 0)!
    let E_good : Set (Set X) := {Z : Set X | Z ⊆ B_set ℓ.castSucc ∧ ¬ (Z ⊆ B_set r_max.succ)}
    have hsub_int : E_good ⊆ dec ⁻¹' {k_out : Fin N | IsInterior y k_out} := by
      rintro Z ⟨hZℓ, hZr⟩
      simp only [Set.mem_preimage, IsInterior]
      -- First: `r_max ∈ filter (bv i = false)`, so `dec Z ≤ r_max = y t_max` AND `dec Z ≥ ℓ = y t_min`!
      let filt := Finset.univ.filter fun i : Fin N => decide (Z ⊆ B_set i.succ) = false
      have hr_mem : r_max ∈ filt := by
        simp [filt, hZr]
      have hfilt_ne : filt.Nonempty := ⟨r_max, hr_mem⟩
      have hdec_eq : dec Z = filt.min' hfilt_ne := by
        dsimp only [dec, Function.comp_apply, postBool]
        exact dif_pos hfilt_ne
      have hdec_le_r : dec Z ≤ r_max := hdec_eq ▸ Finset.min'_le filt r_max hr_mem
      have hℓ_le_dec : ℓ ≤ dec Z := by
        rw [hdec_eq]
        refine Finset.le_min' filt hfilt_ne ℓ fun i hi => ?_
        by_contra hlt_i
        have hi_lt : i < ℓ := lt_of_not_ge hlt_i
        have hisucc_le : i.succ ≤ ℓ.castSucc :=
          Fin.le_iff_val_le_val.mpr (Nat.succ_le_of_lt (Fin.lt_iff_val_lt_val.mp hi_lt))
        have hZ_sub_i : Z ⊆ B_set i.succ := hZℓ.trans (hB_anti hisucc_le)
        have hfalse : decide (Z ⊆ B_set i.succ) = false := (Finset.mem_filter.mp hi).2
        simp [hZ_sub_i] at hfalse
      exact ⟨⟨t_min, ht_min ▸ hℓ_le_dec⟩, ⟨t_max, ht_max ▸ hdec_le_r⟩⟩
    have hnull_compl : (A (encY () y) : Measure (Set X)).real
        {Z : Set X | ¬ (Z ⊆ B_set ℓ.castSucc)} = 0 := by
      refine measureReal_eq_zero_of_ae_not (A (encY () y)) ?_
      filter_upwards [hae_Bℓ] with Z hZ hnot using hnot hZ.2
    have hcov : {Z : Set X | ¬ (Z ⊆ B_set r_max.succ)} ⊆
        E_good ∪ {Z : Set X | ¬ (Z ⊆ B_set ℓ.castSucc)} := by
      intro Z hZr
      by_cases hZℓ : Z ⊆ B_set ℓ.castSucc
      · exact Or.inl ⟨hZℓ, hZr⟩
      · exact Or.inr hZℓ
    have hle_sum : (A (encY () y) : Measure (Set X)).real {Z : Set X | ¬ (Z ⊆ B_set r_max.succ)} ≤
        (A (encY () y) : Measure (Set X)).real E_good +
        (A (encY () y) : Measure (Set X)).real {Z : Set X | ¬ (Z ⊆ B_set ℓ.castSucc)} :=
      (measureReal_mono hcov).trans (measureReal_union_le _ _)
    have hle_target : (A (encY () y) : Measure (Set X)).real E_good ≤
        (A (encY () y) : Measure (Set X)).real (dec ⁻¹' {k_out | IsInterior y k_out}) :=
      measureReal_mono hsub_int
    linarith

/-- Pruning `HasTree C ⊤ d K` to `HasTree C (n : ℕ∞) d K` using the `n`-Helly property. -/
lemma prune_hasTree {X : Type*} {C : LanguageClass X} {n : ℕ}
    (hhelly : ∀ {F : Set (Set X)}, F.Nonempty → F ⊆ infiniteClosure C → (⋂₀ F).Finite →
      ∃ G : Finset (Set X), G.Nonempty ∧ (↑G : Set (Set X)) ⊆ F ∧
        G.card ≤ n ∧ (⋂₀ (↑G : Set (Set X))).Finite)
    {d : ℕ} {K : Set X} (h : HasTree C ⊤ d K) :
    HasTree C (n : ℕ∞) d K := by
  induction h with
  | leaf K hK => exact HasTree.leaf K hK
  | @branch d' K hd' hK F hne _ hsub htree hfin ih =>
      have hF_ic : F ⊆ infiniteClosure C := fun T hT => hasTree_mem_infiniteClosure (htree T hT)
      obtain ⟨G, hGne, hGF, hGcard, hGfin⟩ := hhelly hne hF_ic hfin
      have hencard : (↑G : Set (Set X)).encard ≤ (n : ℕ∞) := by
        rw [Set.encard_coe_eq_coe_finsetCard]
        exact Nat.cast_le.mpr hGcard
      exact HasTree.branch hd' hK (↑G) (Finset.coe_nonempty.mpr hGne) hencard
        (fun T hT => hsub T (hGF hT)) (fun T hT => ih T (hGF hT)) hGfin

/-- Inversion helper for `HasTree C ar (d + 1) K` when `1 ≤ d`, avoiding dependent elimination on `d + 1`. -/
lemma hasTree_succ_inv {X : Type*} {C : LanguageClass X} {ar : ℕ∞} {d : ℕ} (hd : 1 ≤ d) {K : Set X}
    (h : HasTree C ar (d + 1) K) :
    ∃ F : Set (Set X), F.Nonempty ∧ F.encard ≤ ar ∧ (∀ T ∈ F, T ⊆ K) ∧
      (∀ T ∈ F, HasTree C ar d T) ∧ (⋂₀ F).Finite := by
  generalize hk : d + 1 = k at h
  cases h with
  | leaf _ _ => omega
  | @branch d' _ _ _ F hne hcard hsub htree hfin =>
      have hd_eq : d' = d := by omega
      subst hd_eq
      exact ⟨F, hne, hcard, hsub, htree, hfin⟩

/-- Lemma 6.6 (Pure-`HasTree` formulation): Finding a descendant label with finite intersection with `H`. -/
lemma hasTree_exists_finite_inter {X : Type*} {C : LanguageClass X} {ar : ℕ∞} :
    ∀ {s : ℕ} (_ : 1 ≤ s) {m : ℕ} (_ : 1 ≤ m) {H K : Set X},
      H ∈ infiniteClosure C → K ∈ infiniteClosure C → H ⊆ K →
      ¬ HasTree C ar (s + 1) H → HasTree C ar (s + m) K →
      ∃ B ∈ infiniteClosure C, B ⊆ K ∧ (B ∩ H).Finite ∧ HasTree C ar m B := by
  intro s hs
  induction s with
  | zero => omega
  | succ s ih =>
      intro m hm H K hH hK hHK hnotH htreeK
      rcases eq_or_lt_of_le (Nat.succ_le_of_lt (Nat.zero_lt_succ s)) with h_s0 | hs_pos
      · -- Base case `s = 0` (`s + 1 = 1`)
        have hs0 : s = 0 := by omega
        subst hs0
        rw [Nat.add_comm 1 m] at htreeK
        obtain ⟨F, hne, hcard, hsub, htree, hfin⟩ := hasTree_succ_inv hm htreeK
        by_cases hex : ∃ B ∈ F, (B ∩ H).Finite
        · obtain ⟨B, hBF, hBHfin⟩ := hex
          exact ⟨B, hasTree_mem_infiniteClosure (htree B hBF), hsub B hBF, hBHfin, htree B hBF⟩
        · push_neg at hex
          exfalso; apply hnotH
          let F' : Set (Set X) := (· ∩ H) '' F
          obtain ⟨T₀, hT₀⟩ := hne
          refine HasTree.branch (le_refl 1) hH F' ⟨T₀ ∩ H, T₀, hT₀, rfl⟩
            (Set.encard_image_le _ _ |>.trans hcard) ?_ ?_ ?_
          · rintro _ ⟨T, _, rfl⟩; exact Set.inter_subset_right
          · rintro _ ⟨T, hTF, rfl⟩
            have hT_ic := hasTree_mem_infiniteClosure (htree T hTF)
            have hTH_inf : (T ∩ H).Infinite := Set.not_infinite.mp.mt (hex T hTF) |> not_not.mp
            exact HasTree.leaf _ (inter_mem_infiniteClosure C hT_ic hH hTH_inf)
          · refine hfin.subset fun x hx T hTF => ?_
            exact (hx (T ∩ H) ⟨T, hTF, rfl⟩).1
      · -- Step `s ≥ 1` (`s + 1 ≥ 2`)
        have hs1 : 1 ≤ s := by omega
        have heq_sm : s + 1 + m = (s + m) + 1 := by omega
        rw [heq_sm] at htreeK
        obtain ⟨F, hne, hcard, hsub, htree, hfin⟩ := hasTree_succ_inv (by omega : 1 ≤ s + m) htreeK
        by_cases hex : ∃ T ∈ F, (T ∩ H).Finite
        · obtain ⟨T, hTF, hTHfin⟩ := hex
          exact ⟨T, hasTree_mem_infiniteClosure (htree T hTF), hsub T hTF, hTHfin,
            hasTree_le (htree T hTF) hm (by omega)⟩
        · push_neg at hex
          have hex_not_tree : ∃ T ∈ F, ¬ HasTree C ar (s + 1) (T ∩ H) := by
            by_contra hall_tree
            push_neg at hall_tree
            apply hnotH
            let F' : Set (Set X) := (· ∩ H) '' F
            obtain ⟨T₀, hT₀⟩ := hne
            refine HasTree.branch (by omega) hH F' ⟨T₀ ∩ H, T₀, hT₀, rfl⟩
              (Set.encard_image_le _ _ |>.trans hcard) ?_ ?_ ?_
            · rintro _ ⟨T, _, rfl⟩; exact Set.inter_subset_right
            · rintro _ ⟨T, hTF, rfl⟩; exact hall_tree T hTF
            · refine hfin.subset fun x hx T hTF => ?_
              exact (hx (T ∩ H) ⟨T, hTF, rfl⟩).1
          obtain ⟨T, hTF, hnotTH⟩ := hex_not_tree
          have hT_ic := hasTree_mem_infiniteClosure (htree T hTF)
          have hTH_inf : (T ∩ H).Infinite := Set.not_infinite.mp.mt (hex T hTF) |> not_not.mp
          have hTH_ic := inter_mem_infiniteClosure C hT_ic hH hTH_inf
          obtain ⟨B, hB_ic, hBT, hBTH_fin, hBm⟩ :=
            ih hs1 hm hTH_ic hT_ic Set.inter_subset_left hnotTH (htree T hTF)
          have hBH_eq : B ∩ (T ∩ H) = B ∩ H := by
            ext x
            simp only [Set.mem_inter_iff]
            exact ⟨fun ⟨h1, _, h3⟩ => ⟨h1, h3⟩, fun ⟨h1, h3⟩ => ⟨h1, hBT h1, h3⟩⟩
          exact ⟨B, hB_ic, hBT.trans (hsub T hTF), hBH_eq ▸ hBTH_fin, hBm⟩

/-- Helper to build a binary branch `HasTree C 2 (d + 1) K` from two subsets with finite intersection. -/
lemma hasTree_two_branch {X : Type*} {C : LanguageClass X} {d : ℕ} (hd : 1 ≤ d)
    {K A B : Set X} (hK : K ∈ infiniteClosure C) (hAK : A ⊆ K) (hBK : B ⊆ K)
    (htA : HasTree C 2 d A) (htB : HasTree C 2 d B) (hfin : (A ∩ B).Finite) :
    HasTree C 2 (d + 1) K := by
  have henc : ({A, B} : Set (Set X)).encard ≤ 2 := by
    calc ({A, B} : Set (Set X)).encard
        ≤ ({B} : Set (Set X)).encard + 1 := Set.encard_insert_le ({B} : Set (Set X)) A
      _ = 2 := by rw [Set.encard_singleton]; rfl
  refine HasTree.branch hd hK {A, B} ⟨A, by simp⟩ henc ?_ ?_ ?_
  · intro T hT
    rcases Set.mem_insert_iff.mp hT with rfl | hTB
    · exact hAK
    · rw [Set.mem_singleton_iff.mp hTB]; exact hBK
  · intro T hT
    rcases Set.mem_insert_iff.mp hT with rfl | hTB
    · exact htA
    · rw [Set.mem_singleton_iff.mp hTB]; exact htB
  · simpa [Set.sInter_insert, Set.sInter_singleton] using hfin

/-- Lemma 6.7 (Pure-`HasTree` formulation): `¬ HasTree C 2 (q + 1) K → ¬ HasTree C (h : ℕ∞) (2 ^ q) K`. -/
lemma not_hasTree_fin_of_not_hasTree_two {X : Type*} {C : LanguageClass X} (h : ℕ) :
    ∀ {q : ℕ} (_ : 1 ≤ q) {K : Set X},
      K ∈ infiniteClosure C → ¬ HasTree C 2 (q + 1) K → ¬ HasTree C (h : ℕ∞) (2 ^ q) K := by
  intro q hq
  induction q with
  | zero => omega
  | succ q ih =>
      rcases eq_or_lt_of_le (Nat.succ_le_of_lt (Nat.zero_lt_succ q)) with hq0 | hq_pos
      · -- Base case `q = 0` (`q + 1 = 1`, `2 ^ 1 = 2`)
        have hq_zero : q = 0 := by omega
        subst hq_zero
        intro K hK hnot2 htree_h
        change HasTree C (h : ℕ∞) (1 + 1) K at htree_h
        obtain ⟨F, hne, hcard, hsub, htree, hfin⟩ := hasTree_succ_inv (le_refl 1) htree_h
        have hF_fin : F.Finite := Set.finite_of_encard_le_coe hcard
        have hex_r : ∃ r : ℕ, ∃ G : Finset (Set X), G.card = r ∧ G.Nonempty ∧
            (↑G : Set (Set X)) ⊆ F ∧ (⋂₀ (↑G : Set (Set X))).Finite :=
          ⟨hF_fin.toFinset.card, hF_fin.toFinset, rfl,
            (Set.Finite.toFinset_nonempty hF_fin).mpr hne,
            by simp, by simpa using hfin⟩
        set r := Nat.find hex_r
        obtain ⟨G, hGcard, hGne, hGF, hGfin⟩ := Nat.find_spec hex_r
        obtain ⟨A₁, hA₁G⟩ := id hGne
        have hA₁_ic : A₁ ∈ infiniteClosure C :=
          hasTree_mem_infiniteClosure (htree A₁ (hGF (Finset.mem_coe.mpr hA₁G)))
        have hr_ge2 : 2 ≤ r := by
          by_contra hlt2
          have hr1 : G.card = 1 := by
            have := Finset.card_pos.mpr hGne
            omega
          obtain ⟨A₀, rfl⟩ := Finset.card_eq_one.mp hr1
          have hA₀ : A₀ = A₁ := Finset.mem_singleton.mp hA₁G |>.symm
          subst hA₀
          exact hA₁_ic.1 (by simpa using hGfin)
        set G' := G.erase A₁
        have hG'_card : G'.card = r - 1 := by
          have h1 : G'.card + 1 = G.card := Finset.card_erase_add_one hA₁G
          omega
        have hG'_ne : G'.Nonempty := Finset.card_pos.mp (by omega)
        have hG'_sub : (↑G' : Set (Set X)) ⊆ F :=
          (Finset.coe_subset.mpr (Finset.erase_subset _ _)).trans hGF
        have hB_inf : (⋂₀ (↑G' : Set (Set X))).Infinite := by
          by_contra hnotinf
          exact Nat.find_min hex_r (m := r - 1) (by omega)
            ⟨G', hG'_card, hG'_ne, hG'_sub, Set.not_infinite.mp hnotinf⟩
        let B := ⋂₀ (↑G' : Set (Set X))
        have hB_ic : B ∈ infiniteClosure C :=
          sInter_mem_infiniteClosure C (Finset.coe_nonempty.mpr hG'_ne)
            (fun T hT => hasTree_mem_infiniteClosure (htree T (hG'_sub hT))) hB_inf
        obtain ⟨A₂, hA₂G'⟩ := hG'_ne
        have hBK : B ⊆ K :=
          (Set.sInter_subset_of_mem (Finset.mem_coe.mpr hA₂G')).trans
            (hsub A₂ (hG'_sub (Finset.mem_coe.mpr hA₂G')))
        have hAB_eq : A₁ ∩ B = ⋂₀ (↑G : Set (Set X)) := by
          have hins : insert A₁ G' = G := Finset.insert_erase hA₁G
          calc A₁ ∩ B = ⋂₀ (↑(insert A₁ G') : Set (Set X)) := by
                rw [Finset.coe_insert, Set.sInter_insert]
            _ = ⋂₀ (↑G : Set (Set X)) := by rw [hins]
        exact hnot2 (hasTree_two_branch (le_refl 1) hK
          (hsub A₁ (hGF (Finset.mem_coe.mpr hA₁G))) hBK
          (HasTree.leaf A₁ hA₁_ic) (HasTree.leaf B hB_ic) (hAB_eq ▸ hGfin))
      · -- Inductive step `q ≥ 1` (`q + 1 ≥ 2`)
        have hq1 : 1 ≤ q := by omega
        have ih_q : ∀ {K : Set X}, K ∈ infiniteClosure C →
            ¬ HasTree C 2 (q + 1) K → ¬ HasTree C (h : ℕ∞) (2 ^ q) K := fun hK => ih hq1 hK
        set s := 2 ^ q - 1
        have hs_pos : 1 ≤ s := by
          have := two_le_two_pow hq1
          omega
        have hpow_eq : 2 ^ (q + 1) = (2 * s + 1) + 1 := by
          have h1 : 1 ≤ 2 ^ q := Nat.one_le_pow q 2 (by omega)
          have h2 : 2 ^ (q + 1) = 2 * 2 ^ q := by ring
          omega
        intro K hK hnot2 htree_h
        rw [hpow_eq] at htree_h
        obtain ⟨F, hne, hcard, hsub, htree, hfin⟩ := hasTree_succ_inv (by omega : 1 ≤ 2 * s + 1) htree_h
        have hF_fin : F.Finite := Set.finite_of_encard_le_coe hcard
        have hex_r : ∃ r : ℕ, ∃ G : Finset (Set X), G.card = r ∧ G.Nonempty ∧
            (↑G : Set (Set X)) ⊆ F ∧ (⋂₀ (↑G : Set (Set X))).Finite :=
          ⟨hF_fin.toFinset.card, hF_fin.toFinset, rfl,
            (Set.Finite.toFinset_nonempty hF_fin).mpr hne,
            by simp, by simpa using hfin⟩
        set r := Nat.find hex_r
        obtain ⟨G, hGcard, hGne, hGF, hGfin⟩ := Nat.find_spec hex_r
        let eG : Fin r ≃ G := (G.equivFinOfCardEq hGcard).symm
        let A_ch : Fin r → Set X := fun i => (eG i).val
        have hA_F : ∀ i : Fin r, A_ch i ∈ F := fun i => hGF (eG i).2
        have hA_ic : ∀ i : Fin r, A_ch i ∈ infiniteClosure C :=
          fun i => hasTree_mem_infiniteClosure (htree _ (hA_F i))
        have hA_bin : ∀ i : Fin r, HasTree C 2 (q + 1) (A_ch i) := by
          intro i
          by_contra hnot_bin
          have hle_2q : 2 ^ q ≤ 2 * s + 1 := by
            have := Nat.one_le_pow q 2 (by omega)
            omega
          have ht_2q := hasTree_le (htree _ (hA_F i))
            (Nat.one_le_pow q 2 (by omega)) hle_2q
          exact ih_q (hA_ic i) hnot_bin ht_2q
        have hInter_A : (⋂ i : Fin r, A_ch i) = ⋂₀ (↑G : Set (Set X)) := by
          ext x
          simp only [Set.mem_iInter, Set.mem_sInter, Finset.mem_coe]
          exact ⟨fun hx T hTG => by
            have hKeq : A_ch (eG.symm ⟨T, hTG⟩) = T :=
              congrArg Subtype.val (eG.apply_symm_apply ⟨T, hTG⟩)
            exact hKeq ▸ hx (eG.symm ⟨T, hTG⟩),
            fun hx i => hx (A_ch i) (eG i).2⟩
        have hr_ge2 : 2 ≤ r := by
          by_contra hlt2
          have hr1 : r = 1 := by
            have := Finset.card_pos.mpr hGne
            omega
          let i₀ : Fin r := ⟨0, by omega⟩
          have hsingle : (⋂ i : Fin r, A_ch i) = A_ch i₀ := by
            ext x; simp only [Set.mem_iInter]
            exact ⟨fun hx => hx i₀, fun hx i => by
              have : i = i₀ := Fin.ext (by omega)
              rwa [this]⟩
          exact (hA_ic i₀).1 (hsingle ▸ hInter_A ▸ hGfin)
        rcases eq_or_lt_of_le hr_ge2 with hr2_eq | hr_ge3
        · -- `r = 2`: `A_ch 0` and `A_ch 1` directly give `HasTree C 2 (q + 2) K`!
          let i₀ : Fin r := ⟨0, by omega⟩
          let i₁ : Fin r := ⟨1, by omega⟩
          have hpair : A_ch i₀ ∩ A_ch i₁ = ⋂ i : Fin r, A_ch i := by
            ext x; simp only [Set.mem_inter_iff, Set.mem_iInter]
            refine ⟨fun ⟨hx0, hx1⟩ i => ?_, fun hx => ⟨hx i₀, hx i₁⟩⟩
            have hi : i.val = 0 ∨ i.val = 1 := by omega
            rcases hi with h0 | h1
            · exact (show i = i₀ from Fin.ext h0) ▸ hx0
            · exact (show i = i₁ from Fin.ext h1) ▸ hx1
          exact hnot2 (hasTree_two_branch (by omega) hK
            (hsub _ (hA_F i₀)) (hsub _ (hA_F i₁))
            (hA_bin i₀) (hA_bin i₁) (hpair ▸ hInter_A ▸ hGfin))
        · -- `r ≥ 3`: Suffix intersections `Q j = ⋂ (i ≥ j), A_ch i` for `1 ≤ j < r`!
          let Q_suf : ℕ → Set X := fun j => ⋂ (i : Fin r) (_ : j ≤ i.val), A_ch i
          have hQ_ic : ∀ j : ℕ, 1 ≤ j → j < r → Q_suf j ∈ infiniteClosure C := by
            intro j hj1 hjr
            let G_j : Finset (Set X) := (Finset.univ.filter fun i : Fin r => j ≤ i.val).image A_ch
            have hGj_ne : G_j.Nonempty := by
              refine Finset.image_nonempty.mpr ⟨⟨r - 1, by omega⟩, ?_⟩
              simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              omega
            have hGj_card : G_j.card < r := by
              have hsub_erase : (Finset.univ.filter fun i : Fin r => j ≤ i.val) ⊆
                  Finset.univ.erase ⟨0, by omega⟩ := by
                intro i hi
                have hij := (Finset.mem_filter.mp hi).2
                exact Finset.mem_erase.mpr ⟨fun heq => by
                  have : i.val = 0 := congrArg Fin.val heq
                  omega, Finset.mem_univ i⟩
              calc G_j.card
                  ≤ (Finset.univ.filter fun i : Fin r => j ≤ i.val).card := Finset.card_image_le
                _ ≤ (Finset.univ.erase (⟨0, by omega⟩ : Fin r)).card := Finset.card_le_card hsub_erase
                _ = r - 1 := by
                    have := Finset.card_erase_add_one (Finset.mem_univ (⟨0, by omega⟩ : Fin r))
                    rw [Finset.card_univ, Fintype.card_fin] at this
                    omega
                _ < r := by omega
            have hGj_subG : G_j ⊆ G := by
              intro T hT
              obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hT
              exact (eG i).2
            have hGj_eq_Q : ⋂₀ (↑G_j : Set (Set X)) = Q_suf j := by
              ext x
              simp only [Q_suf, G_j, Set.mem_sInter, Finset.mem_coe, Finset.mem_image,
                Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_iInter]
              exact ⟨fun hx i hi => hx (A_ch i) ⟨i, hi, rfl⟩,
                fun hx _ ⟨i, hi, hTi⟩ => hTi ▸ hx i hi⟩
            have hQ_inf : (Q_suf j).Infinite := by
              rw [← hGj_eq_Q]
              by_contra hnotinf
              exact Nat.find_min hex_r hGj_card
                ⟨G_j, rfl, hGj_ne, (Finset.coe_subset.mpr hGj_subG).trans hGF,
                  Set.not_infinite.mp hnotinf⟩
            rw [← hGj_eq_Q]
            exact sInter_mem_infiniteClosure C (Finset.coe_nonempty.mpr hGj_ne)
              (fun T hT => hasTree_mem_infiniteClosure
                (htree T (hGF (Finset.mem_coe.mpr (hGj_subG (Finset.mem_coe.mp hT))))))
              (hGj_eq_Q ▸ hQ_inf)
          have hQ_not_bin : ∀ j : ℕ, 1 ≤ j → j < r → ¬ HasTree C 2 (q + 1) (Q_suf j) := by
            intro j hj1
            induction j with
            | zero => omega
            | succ j ih_j =>
                intro hjr
                rcases eq_or_lt_of_le (Nat.succ_le_of_lt (Nat.zero_lt_succ j)) with hj0 | hj_pos
                · have hj_eq0 : j = 0 := by omega
                  subst hj_eq0
                  intro htQ1
                  let i₀ : Fin r := ⟨0, by omega⟩
                  let i₁ : Fin r := ⟨1, by omega⟩
                  have hQ1_sub_K : Q_suf 1 ⊆ K :=
                    (show Q_suf 1 ⊆ A_ch i₁ from fun x hx => (Set.mem_iInter₂.mp hx) i₁ (le_refl 1)).trans
                      (hsub _ (hA_F i₁))
                  have hA0Q1 : A_ch i₀ ∩ Q_suf 1 = ⋂ i : Fin r, A_ch i := by
                    ext x
                    simp only [Q_suf, Set.mem_inter_iff, Set.mem_iInter]
                    refine ⟨fun ⟨hx0, hx1⟩ i => ?_, fun hx => ⟨hx i₀, fun i _ => hx i⟩⟩
                    by_cases hi0 : i.val = 0
                    · exact (show i = i₀ from Fin.ext hi0) ▸ hx0
                    · exact hx1 i (by omega)
                  exact hnot2 (hasTree_two_branch (by omega) hK
                    (hsub _ (hA_F i₀)) hQ1_sub_K (hA_bin i₀) htQ1 (hA0Q1 ▸ hInter_A ▸ hGfin))
                · have hj_ge1 : 1 ≤ j := by omega
                  have hnot_bin_Qj : ¬ HasTree C 2 (q + 1) (Q_suf j) := ih_j hj_ge1 (by omega)
                  have hnot_h_Qj : ¬ HasTree C (h : ℕ∞) (s + 1) (Q_suf j) := by
                    have hs1_eq : s + 1 = 2 ^ q := by
                      have := Nat.one_le_pow q 2 (by omega)
                      omega
                    rw [hs1_eq]
                    exact ih_q (hQ_ic j hj_ge1 (by omega)) hnot_bin_Qj
                  let ij : Fin r := ⟨j, by omega⟩
                  have hQj_sub_Aj : Q_suf j ⊆ A_ch ij :=
                    fun x hx => (Set.mem_iInter₂.mp hx) ij (le_refl j)
                  have h2s1_eq : 2 * s + 1 = s + (s + 1) := by omega
                  have htAj : HasTree C (h : ℕ∞) (s + (s + 1)) (A_ch ij) :=
                    h2s1_eq ▸ htree _ (hA_F ij)
                  obtain ⟨Bj, hBj_ic, hBj_sub_Aj, hBjQj_fin, htBj_h⟩ :=
                    hasTree_exists_finite_inter hs_pos (by omega : 1 ≤ s + 1)
                      (hQ_ic j hj_ge1 (by omega)) (hA_ic ij) hQj_sub_Aj hnot_h_Qj htAj
                  have htBj_bin : HasTree C 2 (q + 1) Bj := by
                    by_contra hnb_Bj
                    have hs1_eq : s + 1 = 2 ^ q := by
                      have := Nat.one_le_pow q 2 (by omega)
                      omega
                    exact ih_q hBj_ic hnb_Bj (hs1_eq ▸ htBj_h)
                  have hBj_inter_eq : Bj ∩ Q_suf (j + 1) = Bj ∩ Q_suf j := by
                    ext x
                    simp only [Q_suf, Set.mem_inter_iff, Set.mem_iInter]
                    refine ⟨fun ⟨hxB, hxQ⟩ => ⟨hxB, fun i hi => ?_⟩,
                      fun ⟨hxB, hxQ⟩ => ⟨hxB, fun i hi => hxQ i (by omega)⟩⟩
                    rcases eq_or_lt_of_le hi with hij_eq | hij_lt
                    · have hi_eq_ij : i = ij := Fin.ext hij_eq.symm
                      rw [hi_eq_ij]
                      exact hBj_sub_Aj hxB
                    · exact hxQ i (by omega)
                  intro htQj1
                  let ij1 : Fin r := ⟨j + 1, hjr⟩
                  have hQj1_sub_K : Q_suf (j + 1) ⊆ K :=
                    (show Q_suf (j + 1) ⊆ A_ch ij1 from
                      fun x hx => (Set.mem_iInter₂.mp hx) ij1 (le_refl _)).trans
                      (hsub _ (hA_F ij1))
                  exact hnot2 (hasTree_two_branch (by omega) hK
                    (hBj_sub_Aj.trans (hsub _ (hA_F ij))) hQj1_sub_K
                    htBj_bin htQj1 (hBj_inter_eq.symm ▸ hBjQj_fin))
          let ilast : Fin r := ⟨r - 1, by omega⟩
          have hQ_last_eq : Q_suf (r - 1) = A_ch ilast := by
            ext x
            simp only [Q_suf, Set.mem_iInter]
            refine ⟨fun hx => hx ilast (le_refl _), fun hx i hi => ?_⟩
            have : i = ilast := Fin.ext (by dsimp [ilast]; have := i.isLt; omega)
            rwa [this]
          exact hQ_not_bin (r - 1) (by omega) (by omega) (hQ_last_eq.symm ▸ hA_bin ilast)

/-- Extracting two distinct child labels with finite intersection from `HasTree C 2 (d + 1) K`. -/
lemma binary_split_step {X : Type*} {C : LanguageClass X} {d : ℕ} (hd : 1 ≤ d) {K : Set X}
    (h : HasTree C 2 (d + 1) K) :
    ∃ ch : Fin 2 → Set X,
      (∀ b : Fin 2, ch b ∈ infiniteClosure C ∧ ch b ⊆ K ∧ HasTree C 2 d (ch b)) ∧
      (∀ b₁ b₂ : Fin 2, b₁ ≠ b₂ → (ch b₁ ∩ ch b₂).Finite) := by
  obtain ⟨F, hne, hcard, hsub, htree, hfin⟩ := hasTree_succ_inv hd h
  have hF_fin : F.Finite := Set.finite_of_encard_le_coe (hcard.trans_eq (by rfl))
  obtain ⟨T₀, hT₀⟩ := hne
  have hT₀_ic := hasTree_mem_infiniteClosure (htree T₀ hT₀)
  have hex_T₁ : ∃ T₁ ∈ F, T₁ ≠ T₀ := by
    by_contra hall_eq
    push_neg at hall_eq
    have hFeq : F = {T₀} := Set.Subset.antisymm
      (fun T hT => Set.mem_singleton_iff.mpr (hall_eq T hT))
      (Set.singleton_subset_iff.mpr hT₀)
    exact hT₀_ic.1 (by simpa [hFeq] using hfin)
  obtain ⟨T₁, hT₁, hT₁_ne⟩ := hex_T₁
  have hT₁_ic := hasTree_mem_infiniteClosure (htree T₁ hT₁)
  -- Since `{T₀, T₁} ⊆ F`, `T₀ ≠ T₁`, and `F.encard ≤ 2`, `{T₀, T₁} = F`!
  have hpair_eq_F : ({T₀, T₁} : Set (Set X)) = F := by
    have hsub_pair : ({T₀, T₁} : Finset (Set X)) ⊆ hF_fin.toFinset := by
      intro T hT
      rw [Set.Finite.mem_toFinset]
      rcases Finset.mem_insert.mp hT with rfl | h1
      · exact hT₀
      · rw [Finset.mem_singleton.mp h1]; exact hT₁
    have hcard_F : hF_fin.toFinset.card ≤ 2 := by
      have henc := hF_fin.encard_eq_coe_toFinset_card
      rw [henc] at hcard
      exact Nat.cast_le.mp hcard
    have hcard_pair : ({T₀, T₁} : Finset (Set X)).card = 2 :=
      Finset.card_pair hT₁_ne.symm
    have hfin_eq := Finset.eq_of_subset_of_card_le hsub_pair (by omega)
    have hcoe := congrArg (fun S : Finset (Set X) => (↑S : Set (Set X))) hfin_eq
    simpa using hcoe
  have hT01_fin : (T₀ ∩ T₁).Finite := by
    rw [← hpair_eq_F, Set.sInter_insert, Set.sInter_singleton] at hfin
    exact hfin
  let ch : Fin 2 → Set X := fun b => if b = 0 then T₀ else T₁
  refine ⟨ch, ?_, ?_⟩
  · intro b
    fin_cases b
    · simp [ch, hT₀_ic, hsub T₀ hT₀, htree T₀ hT₀]
    · simp [ch, hT₁_ic, hsub T₁ hT₁, htree T₁ hT₁]
  · intro b₁ b₂ hne_b
    fin_cases b₁ <;> fin_cases b₂
    · exact absurd rfl hne_b
    · simpa [ch] using hT01_fin
    · simpa [ch, Set.inter_comm] using hT01_fin
    · exact absurd rfl hne_b

/-- Combining `a`-ary and `b`-ary splits into an `(a * b)`-ary split. -/
lemma prod_split_step {X : Type*} {C : LanguageClass X} {a b d' d : ℕ} {K : Set X}
    {f : Fin a → Set X}
    (hf1 : ∀ i : Fin a, f i ∈ infiniteClosure C ∧ f i ⊆ K ∧ HasTree C 2 d' (f i))
    (hf2 : ∀ i₁ i₂ : Fin a, i₁ ≠ i₂ → (f i₁ ∩ f i₂).Finite)
    (hstep : ∀ {M : Set X}, HasTree C 2 d' M →
      ∃ g : Fin b → Set X,
        (∀ u : Fin b, g u ∈ infiniteClosure C ∧ g u ⊆ M ∧ HasTree C 2 d (g u)) ∧
        (∀ u₁ u₂ : Fin b, u₁ ≠ u₂ → (g u₁ ∩ g u₂).Finite)) :
    ∃ h : Fin (a * b) → Set X,
      (∀ idx : Fin (a * b), h idx ∈ infiniteClosure C ∧ h idx ⊆ K ∧ HasTree C 2 d (h idx)) ∧
      (∀ idx₁ idx₂ : Fin (a * b), idx₁ ≠ idx₂ → (h idx₁ ∩ h idx₂).Finite) := by
  choose g hg1 hg2 using fun i : Fin a => hstep (hf1 i).2.2
  let einv := finProdFinEquiv (m := a) (n := b)
  let h : Fin (a * b) → Set X := fun idx => g (einv.symm idx).1 (einv.symm idx).2
  refine ⟨h, ?_, ?_⟩
  · intro idx
    set p := einv.symm idx
    obtain ⟨h1, h2, h3⟩ := hg1 p.1 p.2
    exact ⟨h1, h2.trans (hf1 p.1).2.1, h3⟩
  · intro idx₁ idx₂ hne
    have hp_ne : einv.symm idx₁ ≠ einv.symm idx₂ := fun heq => hne (einv.symm.injective heq)
    set p₁ := einv.symm idx₁
    set p₂ := einv.symm idx₂
    by_cases hi : p₁.1 = p₂.1
    · have hu_ne : p₁.2 ≠ p₂.2 := fun hu => hp_ne (Prod.ext hi hu)
      change (g p₁.1 p₁.2 ∩ g p₂.1 p₂.2).Finite
      rw [← hi]
      exact hg2 p₁.1 p₁.2 p₂.2 hu_ne
    · refine (hf2 p₁.1 p₂.1 hi).subset ?_
      exact Set.inter_subset_inter (hg1 p₁.1 p₁.2).2.1 (hg1 p₂.1 p₂.2).2.1

/-- Grouping 4 binary levels into a `16`-ary split. -/
lemma four_step_split {X : Type*} {C : LanguageClass X} {d : ℕ} (hd : 1 ≤ d) {K : Set X}
    (h : HasTree C 2 (d + 4) K) :
    ∃ ch : Fin 16 → Set X,
      (∀ b : Fin 16, ch b ∈ infiniteClosure C ∧ ch b ⊆ K ∧ HasTree C 2 d (ch b)) ∧
      (∀ b₁ b₂ : Fin 16, b₁ ≠ b₂ → (ch b₁ ∩ ch b₂).Finite) := by
  have two_step : ∀ {d₀ : ℕ} (_ : 1 ≤ d₀) {M : Set X}, HasTree C 2 (d₀ + 2) M →
      ∃ ch2 : Fin 4 → Set X,
        (∀ b : Fin 4, ch2 b ∈ infiniteClosure C ∧ ch2 b ⊆ M ∧ HasTree C 2 d₀ (ch2 b)) ∧
        (∀ b₁ b₂ : Fin 4, b₁ ≠ b₂ → (ch2 b₁ ∩ ch2 b₂).Finite) := by
    intro d₀ hd₀ M hM
    obtain ⟨f, hf1, hf2⟩ := binary_split_step (d := d₀ + 1) (by omega) hM
    exact prod_split_step (a := 2) (b := 2) hf1 hf2 (binary_split_step hd₀)
  obtain ⟨f4, hf4_1, hf4_2⟩ := two_step (d₀ := d + 2) (by omega) h
  exact prod_split_step (a := 4) (b := 4) hf4_1 hf4_2 (two_step hd)

/-- Recursive `16`-ary tree of depth `N + 1` built from `HasTree C 2 (4 * N + 1) K_root`. -/
structure Tree16 {X : Type*} (C : LanguageClass X) (N : ℕ) (r : ℕ) where
  lbl : (Fin r → Fin 16) → Set X
  h_tree : ∀ p : Fin r → Fin 16, HasTree C 2 (4 * (N - r) + 1) (lbl p)

/-- Lemma 6.10: Ruling out binary nested branching trees of depth `4 * N + 1`. -/
lemma not_hasTree_two_4N_succ {X : Type} [Countable X] {C : LanguageClass X}
    {n : ℕ} (hn : 2 ≤ n) {δ' : ℝ} (hδ0 : 0 ≤ δ') (hδ : (n : ℝ) * δ' ≤ 1 / 100)
    {A : Mechanism X (Set X) n} (hdp : IsDP A 1 δ') (hgen : IsUniformGenerator C A) :
    let m := n - 1
    let N := bnsvS (100 * m) (m - 1)
    ∀ K_root ∈ infiniteClosure C, ¬ HasTree C 2 (4 * N + 1) K_root := by
  intro m N K_root _ htree_root
  have hm_ge1 : 1 ≤ m := by dsimp [m]; omega
  have hm_δ : (m : ℝ) * δ' ≤ 1 / 10 := by
    have hmn : (m : ℝ) ≤ (n : ℝ) := by dsimp [m]; exact_mod_cast Nat.sub_le n 1
    have := mul_le_mul_of_nonneg_right hmn hδ0
    linarith
  obtain ⟨hN_ge2, hno_mech⟩ := no_dp_interior_point hm_ge1 hδ0 hm_δ
  -- Construct node labels `lbl r : (Fin r → Fin 16) → Set X` for `0 ≤ r ≤ N`!
  -- Store parent containment and sibling finite intersections directly in a dependent bundle.
  let step16 : ∀ {r : ℕ} (_ : r < N) (tr : Tree16 C N r),
      {tr' : Tree16 C N (r + 1) //
        (∀ q : Fin (r + 1) → Fin 16, tr'.lbl q ⊆ tr.lbl (Fin.init q)) ∧
        (∀ (p : Fin r → Fin 16) (a₁ a₂ : Fin 16), a₁ ≠ a₂ →
          (tr'.lbl (Fin.snoc p a₁) ∩ tr'.lbl (Fin.snoc p a₂)).Finite)} := by
    intro r hr tr
    have hdepth_eq : 4 * (N - r) + 1 = (4 * (N - (r + 1)) + 1) + 4 := by omega
    choose ch hch1 hch2 using fun p : Fin r → Fin 16 =>
      four_step_split (by omega) (hdepth_eq ▸ tr.h_tree p)
    let lbl' : (Fin (r + 1) → Fin 16) → Set X := fun q => ch (Fin.init q) (q (Fin.last r))
    refine ⟨⟨lbl', fun q => (hch1 (Fin.init q) (q (Fin.last r))).2.2⟩, ?_, ?_⟩
    · intro q
      exact (hch1 (Fin.init q) (q (Fin.last r))).2.1
    · intro p a₁ a₂ hne
      dsimp only [lbl']
      rw [Fin.init_snoc, Fin.snoc_last, Fin.init_snoc, Fin.snoc_last]
      exact hch2 p a₁ a₂ hne
  -- Build the full family of levels `Lbl : ∀ r : ℕ, (Fin r → Fin 16) → Set X` by recursion on `k ≤ N`!
  have hlevels : ∀ k : ℕ, k ≤ N →
      ∃ Lbl : ∀ r : ℕ, (Fin r → Fin 16) → Set X,
        (∀ r : ℕ, r ≤ k → ∀ p : Fin r → Fin 16,
          HasTree C 2 (4 * (N - r) + 1) (Lbl r p)) ∧
        (∀ r : ℕ, r < k → ∀ q : Fin (r + 1) → Fin 16,
          Lbl (r + 1) q ⊆ Lbl r (Fin.init q)) ∧
        (∀ r : ℕ, r < k → ∀ (p : Fin r → Fin 16) (a₁ a₂ : Fin 16), a₁ ≠ a₂ →
          (Lbl (r + 1) (Fin.snoc p a₁) ∩ Lbl (r + 1) (Fin.snoc p a₂)).Finite) := by
    intro k
    induction k with
    | zero =>
        intro _
        refine ⟨fun _ _ => K_root, ?_, ?_, ?_⟩
        · intro r hr0 _
          have : r = 0 := by omega
          subst this; simpa using htree_root
        · intro r hr; omega
        · intro r hr; omega
    | succ k ih =>
        intro hkN
        obtain ⟨Lbl, htr, hsub, hsib⟩ := ih (by omega)
        let tr_k : Tree16 C N k := ⟨Lbl k, htr k (le_refl k)⟩
        obtain ⟨tr_next, hnext_sub, hnext_sib⟩ := step16 (by omega : k < N) tr_k
        let Lbl' : ∀ r : ℕ, (Fin r → Fin 16) → Set X := fun r =>
          if hr : r = k + 1 then hr ▸ tr_next.lbl else Lbl r
        have hLbl'_le : ∀ r : ℕ, r ≤ k → Lbl' r = Lbl r := fun r hr =>
          dif_neg (by omega)
        have hLbl'_top : Lbl' (k + 1) = tr_next.lbl := dif_pos rfl
        refine ⟨Lbl', ?_, ?_, ?_⟩
        · intro r hr p
          rcases eq_or_lt_of_le hr with rfl | hlt
          · rw [hLbl'_top]
            exact tr_next.h_tree p
          · rw [hLbl'_le r (by omega)]
            exact htr r (by omega) p
        · intro r hr q
          rcases eq_or_lt_of_le (Nat.le_of_lt_succ hr) with rfl | hlt
          · rw [hLbl'_top, hLbl'_le r (le_refl r)]
            exact hnext_sub q
          · rw [hLbl'_le (r + 1) (by omega), hLbl'_le r (by omega)]
            exact hsub r hlt q
        · intro r hr p a₁ a₂ hne
          rcases eq_or_lt_of_le (Nat.le_of_lt_succ hr) with rfl | hlt
          · rw [hLbl'_top]
            exact hnext_sib p a₁ a₂ hne
          · rw [hLbl'_le (r + 1) (by omega)]
            exact hsib r hlt p a₁ a₂ hne
  obtain ⟨Lbl, htr, hsub_step, hsib⟩ := hlevels N (le_refl N)
  have hLbl_ic : ∀ (r : ℕ) (_ : r ≤ N) (p : Fin r → Fin 16), Lbl r p ∈ infiniteClosure C :=
    fun r hr p => hasTree_mem_infiniteClosure (htr r hr p)
  -- Prefix truncation map `pref r h Y₀ : Fin r → Fin 16`!
  let pref : ∀ (r : ℕ) (_ : r ≤ N), (Fin N → Fin 16) → (Fin r → Fin 16) :=
    fun r hr Y₀ j => Y₀ ⟨j.val, lt_of_lt_of_le j.isLt hr⟩
  -- Transitive containment along prefixes of `Y₀ : Fin N → Fin 16`!
  have hLbl_anti : ∀ (r₁ r₂ : ℕ) (hr₁ : r₁ ≤ r₂) (hr₂ : r₂ ≤ N) (Y₀ : Fin N → Fin 16),
      Lbl r₂ (pref r₂ hr₂ Y₀) ⊆ Lbl r₁ (pref r₁ (hr₁.trans hr₂) Y₀) := by
    intro r₁ r₂ hr₁ hr₂ Y₀
    induction r₂ with
    | zero =>
        have hr10 : r₁ = 0 := by omega
        subst hr10; exact Set.Subset.rfl
    | succ r₂ ih =>
        rcases eq_or_lt_of_le hr₁ with rfl | hlt
        · exact Set.Subset.rfl
        · have hr₂_lt : r₂ < N := by omega
          have hinit_eq : Fin.init (pref (r₂ + 1) hr₂ Y₀) = pref r₂ hr₂_lt.le Y₀ := by
            ext j; rfl
          have hstep1 : Lbl (r₂ + 1) (pref (r₂ + 1) hr₂ Y₀) ⊆ Lbl r₂ (pref r₂ hr₂_lt.le Y₀) := by
            rw [← hinit_eq]
            exact hsub_step r₂ hr₂_lt (pref (r₂ + 1) hr₂ Y₀)
          exact hstep1.trans (ih (by omega) hr₂_lt.le)
  -- Choose distinct representative points `uRep : Fin n → (Fin N → Fin 16) → X` with `uRep t y ∈ Lbl N y`!
  let LeafIdx := Fin n × (Fin N → Fin 16)
  let M_leaf := Fintype.card LeafIdx
  let eLeaf : Fin M_leaf ≃ LeafIdx := (Fintype.equivFin LeafIdx).symm
  have hex_reps : ∀ (k : ℕ) (hk : k ≤ M_leaf),
      ∃ f : Fin k → X, Function.Injective f ∧
        ∀ idx : Fin k, f idx ∈ Lbl N (eLeaf ⟨idx.val, lt_of_lt_of_le idx.isLt hk⟩).2 := by
    intro k
    induction k with
    | zero => exact fun _ => ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
    | succ k ih =>
        intro hkM
        obtain ⟨f, hfinj, hfmem⟩ := ih (by omega)
        let y_k := (eLeaf ⟨k, hkM⟩).2
        have hy_inf : (Lbl N y_k).Infinite := (hLbl_ic N (le_refl N) y_k).1
        obtain ⟨x_new, hx_in, hx_not_range⟩ := (hy_inf.sdiff (Set.finite_range f)).nonempty
        let f' : Fin (k + 1) → X := fun idx =>
          if h : idx.val < k then f ⟨idx.val, h⟩ else x_new
        refine ⟨f', ?_, ?_⟩
        · intro i₁ i₂ heq
          dsimp only [f'] at heq
          by_cases h1 : i₁.val < k <;> by_cases h2 : i₂.val < k <;>
            simp only [h1, h2, ↓reduceDIte] at heq
          · exact Fin.ext (congrArg (Fin.val : Fin k → ℕ) (hfinj heq))
          · exact absurd ⟨⟨i₁.val, h1⟩, heq⟩ hx_not_range
          · exact absurd ⟨⟨i₂.val, h2⟩, heq.symm⟩ hx_not_range
          · exact Fin.ext (by omega)
        · intro idx
          dsimp only [f']
          split_ifs with hlt
          · exact hfmem ⟨idx.val, hlt⟩
          · have hidx_k : idx.val = k := by omega
            simpa [hidx_k, y_k] using hx_in
  obtain ⟨f_all, hf_all_inj, hf_all_mem⟩ := hex_reps M_leaf (le_refl M_leaf)
  let uRep : Fin n → (Fin N → Fin 16) → X := fun t y => f_all (eLeaf.symm (t, y))
  have huRep_inj : Function.Injective (fun p : Fin n × (Fin N → Fin 16) => uRep p.1 p.2) :=
    fun _ _ heq => eLeaf.symm.injective (hf_all_inj heq)
  have huRep_mem : ∀ (t : Fin n) (y : Fin N → Fin 16), uRep t y ∈ Lbl N y := by
    intro t y
    have h := hf_all_mem (eLeaf.symm (t, y))
    have heq_idx : (⟨(eLeaf.symm (t, y)).val, (eLeaf.symm (t, y)).isLt⟩ : Fin M_leaf) =
        eLeaf.symm (t, y) := rfl
    rw [heq_idx, eLeaf.apply_symm_apply] at h
    exact h
  -- Define randomized encoding + decoding reduction to `Mechanism (Fin N) (Fin N) m`!
  let Θ := (Fin N → Fin 16) × (Fin m → Fin N → Fin 16)
  have : Nonempty Θ := ⟨(fun _ => 0, fun _ _ => 0)⟩
  let wordY : Θ → (Fin m → Fin N) → Fin n → (Fin N → Fin 16) := fun θ x t =>
    if ht0 : t.val = 0 then θ.1
    else
      let i : Fin m := ⟨t.val - 1, by dsimp [m]; omega⟩
      fun j : Fin N => if j.val < (x i).val then θ.1 j else θ.2 i j
  let encX : Θ → (Fin m → Fin N) → (Fin n → X) := fun θ x t =>
    uRep t (wordY θ x t)
  have hencX_inj : ∀ (θ : Θ) (x : Fin m → Fin N), Function.Injective (encX θ x) :=
    fun θ x t₁ t₂ heq =>
      (Prod.ext_iff.mp (@huRep_inj (t₁, wordY θ x t₁) (t₂, wordY θ x t₂) heq)).1
  have hencX_near : ∀ (θ : Θ) {x x' : Fin m → Fin N},
      Neighbors x x' → Near (encX θ x) (encX θ x') := by
    intro θ x x' ⟨i₀, _, hrest⟩
    let t₀ : Fin n := ⟨i₀.val + 1, by dsimp [m] at i₀; omega⟩
    refine near_of_eq_except t₀ fun t ht => ?_
    by_cases ht0 : t.val = 0
    · simp [encX, wordY, ht0]
    · have hi_ne : (⟨t.val - 1, by dsimp [m]; omega⟩ : Fin m) ≠ i₀ := fun heq => by
        have hv : t.val - 1 = i₀.val := congrArg Fin.val heq
        exact ht (Fin.ext (by dsimp [t₀]; omega))
      simp only [encX, wordY, hrest _ hi_ne]
  -- Measurable decoder `dec θ Z : Fin N`: largest `r : Fin N` with `Z ⊆ Lbl r.val (pref r.val _ θ.1)`, else `0`.
  let postMax : (Fin N → Bool) → Fin N := fun bv =>
    if h : (Finset.univ.filter fun r : Fin N => bv r = true).Nonempty then
      (Finset.univ.filter fun r : Fin N => bv r = true).max' h
    else
      ⟨0, by omega⟩
  let dec : Θ → Set X → Fin N := fun θ =>
    postMax ∘ (fun Z r => decide (Z ⊆ Lbl r.val (pref r.val r.isLt.le θ.1)))
  have hdec_meas : ∀ θ : Θ, Measurable (dec θ) := fun θ =>
    (measurable_of_finite postMax).comp
      (measurable_subset_boolVec fun r => Lbl r.val (pref r.val r.isLt.le θ.1))
  let M : Mechanism (Fin N) (Fin N) m := fun x =>
    avgMapPM (fun θ : Θ => A (encX θ x)) dec hdec_meas
  have hM_dp : IsDP M 1 δ' :=
    isDP_avgMap A hdp (by norm_num) hδ0 encX hencX_near dec hdec_meas
  apply hno_mech
  refine ⟨M, hM_dp, fun x => ?_⟩
  rw [avgMapPM_real_apply _ _ _ (DiscreteMeasurableSpace.forall_measurableSet _)]
  have himg_ne : (Finset.univ.image x).Nonempty :=
    Finset.image_nonempty.mpr (Finset.univ_nonempty_iff.mpr ⟨⟨0, hm_ge1⟩⟩)
  let ℓ := (Finset.univ.image x).min' himg_ne
  let w := (Finset.univ.image x).max' himg_ne
  obtain ⟨i_min, _, hi_min⟩ := Finset.mem_image.mp (Finset.min'_mem _ himg_ne)
  obtain ⟨j_max, _, hj_max⟩ := Finset.mem_image.mp (Finset.max'_mem _ himg_ne)
  have hℓ_le : ∀ i : Fin m, ℓ ≤ x i := fun i =>
    Finset.min'_le _ (x i) (Finset.mem_image_of_mem x (Finset.mem_univ i))
  have hx_le_w : ∀ i : Fin m, x i ≤ w := fun i =>
    Finset.le_max' _ (x i) (Finset.mem_image_of_mem x (Finset.mem_univ i))
  let Ev : (Fin w.val → Fin 16) → Fin 16 → Set (Set X) := fun p v =>
    {Z : Set X | Z.Infinite ∧ Z ⊆ Lbl (w.val + 1) (Fin.snoc p v)}
  have hEv_meas : ∀ p v, MeasurableSet (Ev p v) := fun p v =>
    measurableSet_infinite.inter (measurableSet_subset _)
  have hEv_disj : ∀ p, Pairwise fun v₁ v₂ => Disjoint (Ev p v₁) (Ev p v₂) := by
    intro p v₁ v₂ hne
    rw [Set.disjoint_left]
    rintro Z ⟨hZinf, hZ1⟩ ⟨_, hZ2⟩
    exact hZinf ((hsib w.val w.isLt p v₁ v₂ hne).subset (Set.subset_inter hZ1 hZ2))
  have hθ_lb : ∀ θ : Θ,
      1 - (A (encX θ x) : Measure (Set X)).real (Ev (pref w.val w.isLt.le θ.1) (θ.1 w)) ≤
        (A (encX θ x) : Measure (Set X)).real (dec θ ⁻¹' {r_out : Fin N | IsInterior x r_out}) := by
    intro θ
    have hin_ℓ : ∀ t : Fin n, encX θ x t ∈ Lbl ℓ.val (pref ℓ.val ℓ.isLt.le θ.1) := by
      intro t
      have hleaf : encX θ x t ∈ Lbl N (wordY θ x t) := huRep_mem t (wordY θ x t)
      have hpref_eq : pref ℓ.val ℓ.isLt.le (wordY θ x t) = pref ℓ.val ℓ.isLt.le θ.1 := by
        funext j
        dsimp only [pref, wordY]
        by_cases ht0 : t.val = 0
        · rw [dif_pos ht0]
        · rw [dif_neg ht0]
          have hj_lt : j.val < (x ⟨t.val - 1, by dsimp [m]; omega⟩).val :=
            lt_of_lt_of_le j.isLt (Fin.le_iff_val_le_val.mp (hℓ_le _))
          exact if_pos hj_lt
      have hsub_ℓ := hLbl_anti ℓ.val N ℓ.isLt.le (le_refl N) (wordY θ x t)
      have hprefN : pref N (le_refl N) (wordY θ x t) = wordY θ x t := by ext j; rfl
      rw [hprefN, hpref_eq] at hsub_ℓ
      exact hsub_ℓ hleaf
    have hae_ℓ := ae_subset_of_mem_infiniteClosure hgen
      (hLbl_ic ℓ.val ℓ.isLt.le (pref ℓ.val ℓ.isLt.le θ.1)) (hencX_inj θ x) hin_ℓ
    let Good₀ : Set (Set X) :=
      {Z : Set X | Z.Infinite ∧ Z ⊆ Lbl ℓ.val (pref ℓ.val ℓ.isLt.le θ.1)}
    have hGood₀_meas : MeasurableSet Good₀ :=
      measurableSet_infinite.inter (measurableSet_subset _)
    have hGood₀_one : (A (encX θ x) : Measure (Set X)).real Good₀ = 1 :=
      measureReal_eq_one_of_ae (A (encX θ x)) hGood₀_meas hae_ℓ
    have hGood₀_cov : Good₀ ⊆
        (dec θ ⁻¹' {r_out : Fin N | IsInterior x r_out}) ∪
          Ev (pref w.val w.isLt.le θ.1) (θ.1 w) := by
      rintro Z ⟨hZinf, hZℓ⟩
      let filt := Finset.univ.filter fun r : Fin N =>
        decide (Z ⊆ Lbl r.val (pref r.val r.isLt.le θ.1)) = true
      have hℓ_mem : ℓ ∈ filt := by simp [filt, hZℓ]
      have hfilt_ne : filt.Nonempty := ⟨ℓ, hℓ_mem⟩
      have hdec_eq : dec θ Z = filt.max' hfilt_ne := by
        dsimp only [dec, Function.comp_apply, postMax]
        exact dif_pos hfilt_ne
      have hℓ_le_dec : ℓ ≤ dec θ Z := hdec_eq ▸ Finset.le_max' filt ℓ hℓ_mem
      by_cases hdec_le_w : dec θ Z ≤ w
      · left
        exact ⟨⟨i_min, hi_min ▸ hℓ_le_dec⟩, ⟨j_max, hj_max ▸ hdec_le_w⟩⟩
      · right
        have hw_lt_dec : w < dec θ Z := lt_of_not_ge hdec_le_w
        let r_star := dec θ Z
        have hr_mem : r_star ∈ filt := by
          change dec θ Z ∈ filt
          rw [hdec_eq]
          exact Finset.max'_mem filt hfilt_ne
        have hZr : Z ⊆ Lbl r_star.val (pref r_star.val r_star.isLt.le θ.1) := by
          have hb := (Finset.mem_filter.mp hr_mem).2
          simpa using hb
        have hw1_le : w.val + 1 ≤ r_star.val := Nat.succ_le_of_lt (Fin.lt_def.mp hw_lt_dec)
        have hsub_w1 := hLbl_anti (w.val + 1) r_star.val hw1_le r_star.isLt.le θ.1
        have hsnoc_eq : pref (w.val + 1) (Nat.succ_le_of_lt w.isLt) θ.1 =
            Fin.snoc (pref w.val w.isLt.le θ.1) (θ.1 w) := by
          funext j
          refine Fin.lastCases ?_ (fun j₀ => ?_) j
          · simp [pref]
          · simp [pref]
        rw [hsnoc_eq] at hsub_w1
        exact ⟨hZinf, hZr.trans hsub_w1⟩
    have hle_u : (A (encX θ x) : Measure (Set X)).real Good₀ ≤
        (A (encX θ x) : Measure (Set X)).real (dec θ ⁻¹' {r_out : Fin N | IsInterior x r_out}) +
          (A (encX θ x) : Measure (Set X)).real (Ev (pref w.val w.isLt.le θ.1) (θ.1 w)) :=
      (measureReal_mono hGood₀_cov (measure_ne_top _ _)).trans (measureReal_union_le _ _)
    rw [hGood₀_one] at hle_u
    linarith
  -- Bound the average of `(A (encX (Y₀, U) x)).real (Ev (pref w Y₀) (Y₀ w))` over `Y₀ : Fin N → Fin 16` via `swapAtEquiv w`!
  have hEv_avg_ub : ∀ U : Fin m → Fin N → Fin 16,
      ∑ Y₀ : Fin N → Fin 16,
        (A (encX (Y₀, U) x) : Measure (Set X)).real (Ev (pref w.val w.isLt.le Y₀) (Y₀ w)) ≤
        (Fintype.card (Fin N → Fin 16) : ℝ) * (Real.exp 1 / 16 + δ') := by
    intro U
    have hmul_16 : (16 : ℝ) * (∑ Y₀ : Fin N → Fin 16,
          (A (encX (Y₀, U) x) : Measure (Set X)).real (Ev (pref w.val w.isLt.le Y₀) (Y₀ w))) =
        ∑ Y₀ : Fin N → Fin 16, ∑ v : Fin 16,
          (A (encX (Function.update Y₀ w v, U) x) : Measure (Set X)).real
            (Ev (pref w.val w.isLt.le Y₀) v) := by
      have hconst : (16 : ℝ) * (∑ Y₀ : Fin N → Fin 16,
            (A (encX (Y₀, U) x) : Measure (Set X)).real (Ev (pref w.val w.isLt.le Y₀) (Y₀ w))) =
          ∑ p : (Fin N → Fin 16) × Fin 16,
            (A (encX (p.1, U) x) : Measure (Set X)).real (Ev (pref w.val w.isLt.le p.1) (p.1 w)) := by
        rw [Fintype.sum_prod_type]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        norm_num [← Finset.mul_sum]
      rw [hconst, ← Equiv.sum_comp (swapAtEquiv w), Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun Y₀ _ => Finset.sum_congr rfl fun v _ => ?_
      have hupd : (swapAtEquiv w (Y₀, v)).1 = Function.update Y₀ w v := rfl
      have hpref_upd : pref w.val w.isLt.le (Function.update Y₀ w v) = pref w.val w.isLt.le Y₀ := by
        funext j
        dsimp only [pref]
        have hjw : (⟨j.val, lt_of_lt_of_le j.isLt w.isLt.le⟩ : Fin N) ≠ w :=
          fun heq => Nat.ne_of_lt j.isLt (congrArg Fin.val heq)
        exact Function.update_of_ne hjw v Y₀
      rw [hupd, Function.update_self, hpref_upd]
    have hinner : ∀ Y₀ : Fin N → Fin 16,
        (∑ v : Fin 16,
          (A (encX (Function.update Y₀ w v, U) x) : Measure (Set X)).real
            (Ev (pref w.val w.isLt.le Y₀) v)) ≤
          Real.exp 1 + 16 * δ' := by
      intro Y₀
      have hnear_v : ∀ v : Fin 16, Near (encX (Function.update Y₀ w v, U) x) (encX (Y₀, U) x) := by
        intro v
        refine near_of_eq_except ⟨0, by omega⟩ fun t ht => ?_
        have ht0 : ¬ (t.val = 0) := fun h0 => ht (Fin.ext h0)
        dsimp only [encX, wordY]
        rw [dif_neg ht0, dif_neg ht0]
        congr 1
        funext j
        split_ifs with hj
        · have hj_lt_w : j.val < w.val :=
            lt_of_lt_of_le hj (Fin.le_iff_val_le_val.mp (hx_le_w _))
          have hjw : j ≠ w := fun heq => by subst heq; exact Nat.lt_irrefl _ hj_lt_w
          exact Function.update_of_ne hjw v Y₀
        · rfl
      have hdp_v : ∀ v : Fin 16,
          (A (encX (Function.update Y₀ w v, U) x) : Measure (Set X)).real
              (Ev (pref w.val w.isLt.le Y₀) v) ≤
            Real.exp 1 * (A (encX (Y₀, U) x) : Measure (Set X)).real
              (Ev (pref w.val w.isLt.le Y₀) v) + δ' := fun v =>
        isDP_near_le hdp (by norm_num) hδ0 (hnear_v v) (hEv_meas _ v)
      have hdisj_sum : ∑ v : Fin 16,
          (A (encX (Y₀, U) x) : Measure (Set X)).real (Ev (pref w.val w.isLt.le Y₀) v) ≤ 1 :=
        sum_disjoint_real_le_one (A (encX (Y₀, U) x)) _ (hEv_meas _) (hEv_disj _)
      have hexp_sum := mul_le_mul_of_nonneg_left hdisj_sum (Real.exp_pos 1).le
      calc ∑ v : Fin 16,
              (A (encX (Function.update Y₀ w v, U) x) : Measure (Set X)).real
                (Ev (pref w.val w.isLt.le Y₀) v)
          ≤ ∑ v : Fin 16, (Real.exp 1 * (A (encX (Y₀, U) x) : Measure (Set X)).real
              (Ev (pref w.val w.isLt.le Y₀) v) + δ') := Finset.sum_le_sum fun v _ => hdp_v v
        _ = Real.exp 1 * (∑ v : Fin 16, (A (encX (Y₀, U) x) : Measure (Set X)).real
              (Ev (pref w.val w.isLt.le Y₀) v)) + 16 * δ' := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
              Fintype.card_fin, nsmul_eq_mul]
            norm_num
        _ ≤ Real.exp 1 + 16 * δ' := by linarith
    have hsum16 : (16 : ℝ) * (∑ Y₀ : Fin N → Fin 16,
          (A (encX (Y₀, U) x) : Measure (Set X)).real (Ev (pref w.val w.isLt.le Y₀) (Y₀ w))) ≤
        (Fintype.card (Fin N → Fin 16) : ℝ) * (Real.exp 1 + 16 * δ') := by
      rw [hmul_16]
      calc ∑ Y₀ : Fin N → Fin 16, ∑ v : Fin 16, _
          ≤ ∑ _Y₀ : Fin N → Fin 16, (Real.exp 1 + 16 * δ') :=
            Finset.sum_le_sum fun Y₀ _ => hinner Y₀
        _ = (Fintype.card (Fin N → Fin 16) : ℝ) * (Real.exp 1 + 16 * δ') := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    linarith
  -- Sum `hθ_lb` over all `θ : Θ` and divide by `Fintype.card Θ`!
  have hcardΘ_pos : (0 : ℝ) < (Fintype.card Θ : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hcardΘ_ne : (Fintype.card Θ : ℝ) ≠ 0 := hcardΘ_pos.ne'
  have hcardΘ_eq : (Fintype.card Θ : ℝ) =
      (Fintype.card (Fin N → Fin 16) : ℝ) * (Fintype.card (Fin m → Fin N → Fin 16) : ℝ) := by
    dsimp [Θ]; rw [Fintype.card_prod, Nat.cast_mul]
  have hEv_total : ∑ θ : Θ,
      (A (encX θ x) : Measure (Set X)).real (Ev (pref w.val w.isLt.le θ.1) (θ.1 w)) ≤
      (Fintype.card Θ : ℝ) * (Real.exp 1 / 16 + δ') := by
    dsimp [Θ]
    rw [Fintype.sum_prod_type_right]
    calc ∑ U : Fin m → Fin N → Fin 16, ∑ Y₀ : Fin N → Fin 16,
            (A (encX (Y₀, U) x) : Measure (Set X)).real (Ev (pref w.val w.isLt.le Y₀) (Y₀ w))
        ≤ ∑ _U : Fin m → Fin N → Fin 16,
            (Fintype.card (Fin N → Fin 16) : ℝ) * (Real.exp 1 / 16 + δ') :=
          Finset.sum_le_sum fun U _ => hEv_avg_ub U
      _ = (Fintype.card Θ : ℝ) * (Real.exp 1 / 16 + δ') := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcardΘ_eq]
          ring
  have hsum_target_lb : (Fintype.card Θ : ℝ) * (1 - (Real.exp 1 / 16 + δ')) ≤
      ∑ θ : Θ, (A (encX θ x) : Measure (Set X)).real (dec θ ⁻¹' {r_out | IsInterior x r_out}) := by
    have h1 : ∑ θ : Θ, (1 - (A (encX θ x) : Measure (Set X)).real (Ev (pref w.val w.isLt.le θ.1) (θ.1 w))) ≤
        ∑ θ : Θ, (A (encX θ x) : Measure (Set X)).real (dec θ ⁻¹' {r_out | IsInterior x r_out}) :=
      Finset.sum_le_sum fun θ _ => hθ_lb θ
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at h1
    linarith
  have hexp_lt3 : Real.exp 1 < 3 := by
    have := Real.exp_one_lt_d9
    linarith
  have hδ_small : δ' ≤ 1 / 100 := by
    have hn_ge1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
    have := mul_le_mul_of_nonneg_right hn_ge1 hδ0
    linarith
  have htwo_thirds : (2 / 3 : ℝ) ≤ 1 - (Real.exp 1 / 16 + δ') := by linarith
  calc (2 / 3 : ℝ)
      ≤ 1 - (Real.exp 1 / 16 + δ') := htwo_thirds
    _ = ((Fintype.card Θ : ℝ)⁻¹) * ((Fintype.card Θ : ℝ) * (1 - (Real.exp 1 / 16 + δ'))) := by
        field_simp [hcardΘ_ne]
    _ ≤ ((Fintype.card Θ : ℝ)⁻¹) *
          ∑ θ : Θ, (A (encX θ x) : Measure (Set X)).real
            (dec θ ⁻¹' {r_out | IsInterior x r_out}) :=
        mul_le_mul_of_nonneg_left hsum_target_lb (inv_nonneg.mpr hcardΘ_pos.le)

/-- Complete lower bound direction of Theorem 1.1! -/
theorem lower_bound {X : Type} [Countable X] (C : LanguageClass X)
    (hpug : PrivatelyUniformlyGeneratable C) :
    closureDim C < ⊤ ∧ nbDim C ⊤ < ⊤ := by
  obtain ⟨n₀, _, δ, A, htend, hprop⟩ := hpug
  -- Pick a single fixed `n ≥ max n₀ 2` such that `(n : ℝ) * δ n < 1 / 100`.
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.mp htend (1 / 100) (by norm_num)
  let n : ℕ := max (max n₀ 2) N₁
  have hn_n0 : n₀ ≤ n := le_trans (le_max_left n₀ 2) (le_max_left _ N₁)
  have hn_ge2 : 2 ≤ n := le_trans (le_max_right n₀ 2) (le_max_left _ N₁)
  have hn_N1 : N₁ ≤ n := le_max_right _ N₁
  obtain ⟨hdp_raw, hgen⟩ := hprop n hn_n0
  let δ' : ℝ := max (δ n) 0
  have hδ0 : 0 ≤ δ' := le_max_right _ 0
  have hnδ_lt : (n : ℝ) * δ' ≤ 1 / 100 := by
    have hd := hN₁ n hn_N1
    rw [Real.dist_eq, sub_zero] at hd
    have hlt : (n : ℝ) * δ n < 1 / 100 := (abs_lt.mp hd).2
    by_cases hsign : 0 ≤ δ n
    · have : δ' = δ n := max_eq_left hsign
      rw [this]; exact hlt.le
    · have : δ' = 0 := max_eq_right (le_of_not_ge hsign)
      rw [this, mul_zero]; norm_num
  have hdp : IsDP (A n) 1 δ' := by
    intro S S' hnb O hO
    have h1 := hdp_raw S S' hnb O hO
    have hle : δ n ≤ δ' := le_max_left _ 0
    linarith
  -- 1. `closureDim C < ⊤` by Lemma 6.3!
  have hcdim : closureDim C < ⊤ := lower_closureDim_lt_top hgen
  -- 2. `nbDim C ⊤ < ⊤` by Lemma 6.5 + Pruning + Lemma 6.7 + Lemma 6.10!
  have hhelly : ∀ {F : Set (Set X)}, F.Nonempty → F ⊆ infiniteClosure C → (⋂₀ F).Finite →
      ∃ G : Finset (Set X), G.Nonempty ∧ (↑G : Set (Set X)) ⊆ F ∧
        G.card ≤ n ∧ (⋂₀ (↑G : Set (Set X))).Finite :=
    fun hne hF hfin => lower_helly_infiniteClosure hn_ge2 hδ0 (by linarith) hdp hgen hne hF hfin
  have hnot_bin := not_hasTree_two_4N_succ hn_ge2 hδ0 hnδ_lt hdp hgen
  let N_bnsv := bnsvS (100 * (n - 1)) (n - 1 - 1)
  let D_bound := 2 ^ (4 * N_bnsv)
  have hD_pos : 1 ≤ D_bound := Nat.one_le_pow _ 2 (by omega)
  have hnb_le : nbDim C ⊤ ≤ ((D_bound - 1 : ℕ) : ℕ∞) := by
    unfold nbDim rank
    refine iSup₂_le fun K hK => iSup₂_le fun d hd => ?_
    by_contra hnot
    have hd_ge : D_bound ≤ d := by
      have hlt : ((D_bound - 1 : ℕ) : ℕ∞) < (d : ℕ∞) := lt_of_not_ge hnot
      have := Nat.cast_lt.mp hlt
      omega
    have ht_top : HasTree C ⊤ D_bound K := hasTree_le hd hD_pos hd_ge
    have ht_n : HasTree C (n : ℕ∞) D_bound K := prune_hasTree (@hhelly) ht_top
    have hq_pos : 1 ≤ 4 * N_bnsv := by
      obtain ⟨hN2, _⟩ := no_dp_interior_point (m := n - 1) (by omega) hδ0 (by
        have hmn : ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.sub_le n 1
        have := mul_le_mul_of_nonneg_right hmn hδ0
        linarith)
      change 2 ≤ N_bnsv at hN2
      omega
    exact not_hasTree_fin_of_not_hasTree_two n hq_pos hK (hnot_bin K hK) ht_n
  exact ⟨hcdim, lt_of_le_of_lt hnb_le (ENat.natCast_lt_top _)⟩

end LowerBound
end PrivGenProof

open MeasureTheory PrivateUniformGen.Characterization

theorem solution {X : Type} [Countable X] (C : LanguageClass X) :
  PrivatelyUniformlyGeneratable C ↔ closureDim C < ⊤ ∧ nbDim C ⊤ < ⊤ :=
  ⟨PrivGenProof.lower_bound C, fun ⟨hc, hnb⟩ => PrivGenProof.upper_bound C hc hnb⟩
