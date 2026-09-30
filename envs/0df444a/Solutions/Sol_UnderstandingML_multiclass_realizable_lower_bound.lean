-- Prove2me | solution 1 for UnderstandingML.multiclass_realizable_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-25T21:54:27.996627+00:00
-- url     : https://prove2.me/submissions/cc52459c-af85-45a4-bb0e-c3af8d8fcf33

import Definitions.Def_UnderstandingML_MulticlassLearnability

open MeasureTheory UnderstandingML

universe u v

namespace RealizableLowerAux

open Classical

variable {X : Type*} {Y : Type*}

/-- A class of finite Natarajan dimension `d` shatters a set of size exactly `d`. -/
lemma exists_nshatters_card (H : Set (X → Y)) (d : ℕ) (hd : ndim H = d) (hd1 : 1 ≤ d) :
    ∃ C : Finset X, NShatters H C ∧ C.card = d := by
  by_contra hne
  push Not at hne
  have hle : ndim H ≤ ((d - 1 : ℕ) : ℕ∞) := by
    unfold ndim
    refine iSup₂_le fun C hC ↦ ?_
    have h1 : (C.card : ℕ∞) ≤ d := hd ▸
      le_iSup₂_of_le (f := fun (C : Finset X) (_ : NShatters H C) ↦ (C.card : ℕ∞)) C hC le_rfl
    have h2 := hne C hC
    norm_cast at h1 ⊢
    omega
  rw [hd] at hle
  norm_cast at hle
  omega

/-- The hard distribution: a heavy point `a` of mass `1 - η` and the points of `L`, each of
mass `η / |L|`. -/
noncomputable def lbDist [MeasurableSpace X] (a : X) (L : Finset X) (η : ℝ) : Measure X :=
  ENNReal.ofReal (1 - η) • Measure.dirac a +
    ∑ c ∈ L, ENNReal.ofReal (η / L.card) • Measure.dirac c

section Dist

variable [MeasurableSpace X] [MeasurableSingletonClass X]

lemma lbDist_apply (a : X) (L : Finset X) (η : ℝ) (s : Set X) :
    lbDist a L η s = ENNReal.ofReal (1 - η) * s.indicator 1 a +
      ∑ c ∈ L, ENNReal.ofReal (η / L.card) * s.indicator 1 c := by
  simp only [lbDist, Measure.add_apply, Measure.smul_apply, smul_eq_mul, Measure.dirac_apply,
    Measure.coe_finsetSum, Finset.sum_apply]

lemma lbDist_isProb {a : X} {L : Finset X} (hL : L.Nonempty) {η : ℝ}
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) : IsProbabilityMeasure (lbDist a L η) := by
  constructor
  rw [lbDist_apply]
  simp only [Set.indicator_univ, Pi.one_apply, mul_one, Finset.sum_const, nsmul_eq_mul]
  have hn : (0 : ℝ) < L.card := by exact_mod_cast hL.card_pos
  rw [show ((L.card : ℕ) : ENNReal) = ENNReal.ofReal (L.card : ℝ) by rw [ENNReal.ofReal_natCast],
    ← ENNReal.ofReal_mul hn.le, mul_div_cancel₀ _ hn.ne',
    ← ENNReal.ofReal_add (by linarith) hη0]
  simp

lemma lbDist_ge_card (a : X) (L : Finset X) (η : ℝ) (T : Finset X) (hT : T ⊆ L) :
    ENNReal.ofReal (η / L.card) * T.card ≤ lbDist a L η (T : Set X) := by
  rw [lbDist_apply]
  refine le_trans ?_ le_add_self
  have : ∑ c ∈ L, ENNReal.ofReal (η / L.card) * (T : Set X).indicator 1 c =
      ∑ c ∈ T, ENNReal.ofReal (η / L.card) := by
    rw [← Finset.sum_subset hT]
    · refine Finset.sum_congr rfl fun c hc ↦ ?_
      simp [Finset.mem_coe.mpr hc]
    · intro c _ hc
      simp [hc]
  rw [this, Finset.sum_const, nsmul_eq_mul, mul_comm]

lemma lbDist_heavy {a : X} {L : Finset X} (ha : a ∉ L) (η : ℝ) :
    lbDist a L η {a} = ENNReal.ofReal (1 - η) := by
  rw [lbDist_apply]
  have : ∀ c ∈ L, ENNReal.ofReal (η / L.card) * ({a} : Set X).indicator 1 c = 0 := by
    intro c hc
    have : c ≠ a := fun h ↦ ha (h ▸ hc)
    simp [this]
  rw [Finset.sum_eq_zero this]
  simp

lemma lbDist_light {a : X} {L : Finset X} (ha : a ∉ L) (hL : L.Nonempty) {η : ℝ} :
    lbDist a L η {a}ᶜ = ENNReal.ofReal η := by
  rw [lbDist_apply]
  have : ∀ c ∈ L, ENNReal.ofReal (η / L.card) * ({a}ᶜ : Set X).indicator 1 c =
      ENNReal.ofReal (η / L.card) := by
    intro c hc
    have : c ≠ a := fun h ↦ ha (h ▸ hc)
    simp [this]
  rw [Finset.sum_congr rfl this]
  simp only [Set.indicator_of_notMem (Set.notMem_compl_iff.mpr (Set.mem_singleton a)),
    mul_zero, zero_add, Finset.sum_const, nsmul_eq_mul]
  have hn : (0 : ℝ) < L.card := by exact_mod_cast hL.card_pos
  rw [show ((L.card : ℕ) : ENNReal) = ENNReal.ofReal (L.card : ℝ) by rw [ENNReal.ofReal_natCast],
    ← ENNReal.ofReal_mul hn.le, mul_div_cancel₀ _ hn.ne']

lemma lbDist_outside (a : X) (L : Finset X) (η : ℝ) :
    lbDist a L η ((insert a L : Finset X) : Set X)ᶜ = 0 := by
  rw [lbDist_apply]
  have ha : a ∉ (((insert a L : Finset X) : Set X)ᶜ) := by simp
  rw [Set.indicator_of_notMem ha, mul_zero, zero_add]
  refine Finset.sum_eq_zero fun c hc ↦ ?_
  have : c ∉ (((insert a L : Finset X) : Set X)ᶜ) := by simp [hc]
  rw [Set.indicator_of_notMem this, mul_zero]

end Dist

/-- The unseen points of `L`: those not hit by the sample `xs`. -/
noncomputable def unseen {m : ℕ} (L : Finset X) (xs : Fin m → X) : Finset X := by
  classical exact L.filter (fun c ↦ ∀ j, xs j ≠ c)

section Core

variable [MeasurableSpace X] [MeasurableSingletonClass X]

/-- Samples on which the learner fails for the target `t B`. -/
def failSet (D : Measure X) (A : Learner (X × Y) (X → Y)) (m : ℕ) (ε : ℝ) (t : X → Y) :
    Set (Fin m → X) :=
  {xs | ENNReal.ofReal ε < D {x | A m (fun j ↦ (xs j, t (xs j))) x ≠ t x}}

variable {a : X} {L : Finset X} {f₀ f₁ : X → Y} {t : Finset X → X → Y}

/-- The pairing step: flipping the labels on the unseen points does not change the sample, and
the learner must err on at least half of the unseen points for one of the two targets. -/
lemma fail_or_fail_flip (A : Learner (X × Y) (X → Y)) (m : ℕ) {ε : ℝ} (hε : 0 < ε)
    (hL : L.Nonempty)
    (hf : ∀ x ∈ L, f₀ x ≠ f₁ x)
    (ht_a : ∀ B ⊆ L, t B a = f₀ a) (ht_in : ∀ B ⊆ L, ∀ x ∈ B, t B x = f₀ x)
    (ht_out : ∀ B ⊆ L, ∀ x ∈ L, x ∉ B → t B x = f₁ x)
    (xs : Fin m → X) (hxs : ∀ j, xs j ∈ insert a L)
    (hU : L.card ≤ 2 * (unseen L xs).card) (B : Finset X) (hB : B ⊆ L) :
    xs ∈ failSet (lbDist a L (8 * ε)) A m ε (t B) ∨
      xs ∈ failSet (lbDist a L (8 * ε)) A m ε (t (symmDiff B (unseen L xs))) := by
  set U := unseen L xs with hUdef
  set B' := symmDiff B U with hB'def
  set D := lbDist a L (8 * ε) with hD
  have hUL : U ⊆ L := Finset.filter_subset _ _
  have hB'L : B' ⊆ L := by
    intro c hc
    rcases Finset.mem_symmDiff.1 hc with ⟨h, -⟩ | ⟨h, -⟩
    · exact hB h
    · exact hUL h
  have hsame : (fun j ↦ (xs j, t B (xs j))) = (fun j ↦ (xs j, t B' (xs j))) := by
    funext j
    refine Prod.ext rfl ?_
    rcases Finset.mem_insert.1 (hxs j) with h | h
    · simp only [h, ht_a B hB, ht_a B' hB'L]
    · have hnU : xs j ∉ U := by
        simp only [hUdef, unseen, Finset.mem_filter, not_and, not_forall, not_not]
        exact fun _ ↦ ⟨j, rfl⟩
      by_cases hb : xs j ∈ B
      · have : xs j ∈ B' := Finset.mem_symmDiff.2 (Or.inl ⟨hb, hnU⟩)
        simp only [ht_in B hB _ hb, ht_in B' hB'L _ this]
      · have : xs j ∉ B' := by simp [hB'def, Finset.mem_symmDiff, hb, hnU]
        simp only [ht_out B hB _ h hb, ht_out B' hB'L _ h this]
  set g := A m (fun j ↦ (xs j, t B (xs j))) with hg
  have hdiff : ∀ c ∈ U, g c ≠ t B c ∨ g c ≠ t B' c := by
    intro c hc
    have hcL := hUL hc
    by_contra h
    push Not at h
    have hne : t B c ≠ t B' c := by
      by_cases hb : c ∈ B
      · have : c ∉ B' := by simp [hB'def, Finset.mem_symmDiff, hb, hc]
        rw [ht_in B hB c hb, ht_out B' hB'L c hcL this]; exact hf c hcL
      · have : c ∈ B' := by simp [hB'def, Finset.mem_symmDiff, hb, hc]
        rw [ht_out B hB c hcL hb, ht_in B' hB'L c this]; exact (hf c hcL).symm
    exact hne (h.1.symm.trans h.2)
  set M1 := U.filter (fun c ↦ g c ≠ t B c) with hM1
  set M2 := U.filter (fun c ↦ g c ≠ t B' c) with hM2
  have hM : U.card ≤ M1.card + M2.card := by
    calc U.card ≤ (M1 ∪ M2).card := Finset.card_le_card (fun c hc ↦ by
            rcases hdiff c hc with h | h
            · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hc, h⟩)
            · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hc, h⟩))
      _ ≤ M1.card + M2.card := Finset.card_union_le _ _
  have hn : (0 : ℝ) < L.card := by exact_mod_cast hL.card_pos
  have herr : ∀ (h : X → Y) (M : Finset X), M ⊆ L → (∀ c ∈ M, g c ≠ h c) →
      L.card ≤ 4 * M.card → ENNReal.ofReal ε < D {x | g x ≠ h x} := by
    intro h M hML hMg hcard
    have hcard' : (L.card : ℝ) ≤ 4 * M.card := by exact_mod_cast hcard
    calc ENNReal.ofReal ε < ENNReal.ofReal (8 * ε / L.card * M.card) := by
          rw [ENNReal.ofReal_lt_ofReal_iff_of_nonneg hε.le]
          rw [div_mul_eq_mul_div, lt_div_iff₀ hn]
          nlinarith
      _ = ENNReal.ofReal (8 * ε / L.card) * M.card := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
      _ ≤ D (M : Set X) := lbDist_ge_card a L _ M hML
      _ ≤ D {x | g x ≠ h x} := measure_mono fun c hc ↦ hMg c hc
  by_cases h1 : L.card ≤ 4 * M1.card
  · left
    exact herr (t B) M1 ((Finset.filter_subset _ _).trans hUL)
      (fun c hc ↦ (Finset.mem_filter.1 hc).2) h1
  · right
    have h2 : L.card ≤ 4 * M2.card := by omega
    show ENNReal.ofReal ε < D {x | A m (fun j ↦ (xs j, t B' (xs j))) x ≠ t B' x}
    rw [← hsame]
    exact herr (t B') M2 ((Finset.filter_subset _ _).trans hUL)
      (fun c hc ↦ (Finset.mem_filter.1 hc).2) h2

/-- Counting over all targets: at least half of them fail on a good sample. -/
lemma card_fail_ge (A : Learner (X × Y) (X → Y)) (m : ℕ) {ε : ℝ} (hε : 0 < ε)
    (hL : L.Nonempty)
    (hf : ∀ x ∈ L, f₀ x ≠ f₁ x)
    (ht_a : ∀ B ⊆ L, t B a = f₀ a) (ht_in : ∀ B ⊆ L, ∀ x ∈ B, t B x = f₀ x)
    (ht_out : ∀ B ⊆ L, ∀ x ∈ L, x ∉ B → t B x = f₁ x)
    (xs : Fin m → X) (hxs : ∀ j, xs j ∈ insert a L)
    (hU : L.card ≤ 2 * (unseen L xs).card) (T : Finset X → Set (Fin m → X))
    (hT : ∀ B ⊆ L, failSet (lbDist a L (8 * ε)) A m ε (t B) ⊆ T B) :
    (2 : ENNReal) ^ L.card ≤ 2 * ∑ B ∈ L.powerset, (T B).indicator 1 xs := by
  set U := unseen L xs with hUdef
  have hUL : U ⊆ L := Finset.filter_subset _ _
  set f : Finset X → ENNReal := fun B ↦ (T B).indicator 1 xs with hf'
  have hσ : ∀ B ∈ L.powerset, symmDiff B U ∈ L.powerset := by
    intro B hB
    rw [Finset.mem_powerset] at hB ⊢
    intro c hc
    rcases Finset.mem_symmDiff.1 hc with ⟨h, -⟩ | ⟨h, -⟩
    · exact hB h
    · exact hUL h
  have hinv : ∀ B : Finset X, symmDiff (symmDiff B U) U = B := fun B ↦ symmDiff_symmDiff_cancel_right U B
  have hswap : ∑ B ∈ L.powerset, f (symmDiff B U) = ∑ B ∈ L.powerset, f B :=
    Finset.sum_nbij' (fun B ↦ symmDiff B U) (fun B ↦ symmDiff B U) hσ hσ
      (fun B _ ↦ hinv B) (fun B _ ↦ hinv B) (fun B _ ↦ rfl)
  have hone : ∀ B ∈ L.powerset, (1 : ENNReal) ≤ f B + f (symmDiff B U) := by
    intro B hB
    rw [Finset.mem_powerset] at hB
    rcases fail_or_fail_flip A m hε hL hf ht_a ht_in ht_out xs hxs hU B hB with h | h
    · have : xs ∈ T B := hT B hB h
      simp [hf', this]
    · have : xs ∈ T (symmDiff B U) := hT _ (Finset.mem_powerset.1 (hσ B (Finset.mem_powerset.2 hB))) h
      simp [hf', this]
  calc (2 : ENNReal) ^ L.card = ∑ B ∈ L.powerset, (1 : ENNReal) := by
        rw [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul, mul_one]; push_cast; rfl
    _ ≤ ∑ B ∈ L.powerset, (f B + f (symmDiff B U)) := Finset.sum_le_sum hone
    _ = 2 * ∑ B ∈ L.powerset, f B := by rw [Finset.sum_add_distrib, hswap, two_mul]

/-- The measure-theoretic core: the probability of a good event is at most `2δ`. -/
lemma measure_good_le (A : Learner (X × Y) (X → Y)) (m : ℕ) {ε δ : ℝ} (hε : 0 < ε)
    (hε1 : 8 * ε ≤ 1) (hL : L.Nonempty)
    (hf : ∀ x ∈ L, f₀ x ≠ f₁ x)
    (ht_a : ∀ B ⊆ L, t B a = f₀ a) (ht_in : ∀ B ⊆ L, ∀ x ∈ B, t B x = f₀ x)
    (ht_out : ∀ B ⊆ L, ∀ x ∈ L, x ∉ B → t B x = f₁ x) [MeasurableSpace Y]
    (htm : ∀ B ⊆ L, Measurable (t B))
    (hPAC : ∀ B ⊆ L, iidLaw ((lbDist a L (8 * ε)).map (fun x ↦ (x, t B x))) m
      {S | ENNReal.ofReal ε < lbDist a L (8 * ε) {x | A m S x ≠ t B x}} ≤ ENNReal.ofReal δ)
    (G : Set (Fin m → X)) (hGm : MeasurableSet G)
    (hG : ∀ xs ∈ G, (∀ j, xs j ∈ insert a L) ∧ L.card ≤ 2 * (unseen L xs).card) :
    iidLaw (lbDist a L (8 * ε)) m G ≤ 2 * ENNReal.ofReal δ := by
  set D := lbDist a L (8 * ε) with hD
  have hDprob : IsProbabilityMeasure D := lbDist_isProb hL (by linarith) hε1
  set μ := iidLaw D m with hμ
  set E : Finset X → Set (Fin m → X) := fun B ↦ failSet D A m ε (t B) with hEdef
  set T : Finset X → Set (Fin m → X) := fun B ↦ toMeasurable μ (E B) with hTdef
  have hE : ∀ B ⊆ L, μ (E B) ≤ ENNReal.ofReal δ := by
    intro B hB
    have hφ : Measurable (fun x ↦ (x, t B x)) := measurable_id.prodMk (htm B hB)
    have : IsProbabilityMeasure (D.map (fun x ↦ (x, t B x))) :=
      Measure.isProbabilityMeasure_map hφ.aemeasurable
    have hmap : iidLaw (D.map (fun x ↦ (x, t B x))) m =
        μ.map (fun xs j ↦ (xs j, t B (xs j))) := by
      rw [hμ, iidLaw, iidLaw, Measure.pi_map_pi (fun _ ↦ hφ.aemeasurable)]
    refine le_trans ?_ (hPAC B hB)
    rw [hmap]
    exact Measure.le_map_apply (measurable_pi_lambda _ fun j ↦ hφ.comp
      (measurable_pi_apply j)).aemeasurable _
  have hpt : ∀ xs, (2 : ENNReal) ^ L.card * G.indicator 1 xs ≤
      2 * ∑ B ∈ L.powerset, (T B).indicator 1 xs := by
    intro xs
    by_cases hx : xs ∈ G
    · rw [Set.indicator_of_mem hx, Pi.one_apply, mul_one]
      exact card_fail_ge A m hε hL hf ht_a ht_in ht_out xs (hG xs hx).1 (hG xs hx).2 T
        (fun B _ ↦ subset_toMeasurable μ (E B))
    · simp [hx]
  have hTm : ∀ B, MeasurableSet (T B) := fun B ↦ measurableSet_toMeasurable μ (E B)
  have hint := lintegral_mono (μ := μ) hpt
  rw [lintegral_const_mul _ (measurable_one.indicator hGm), lintegral_indicator_one hGm,
    lintegral_const_mul _ (Finset.measurable_sum _ fun B _ ↦ measurable_one.indicator (hTm B)),
    lintegral_finsetSum _ (fun B _ ↦ measurable_one.indicator (hTm B))] at hint
  have hsum : ∑ B ∈ L.powerset, ∫⁻ xs, (T B).indicator 1 xs ∂μ ≤
      ∑ B ∈ L.powerset, ENNReal.ofReal δ := by
    refine Finset.sum_le_sum fun B hB ↦ ?_
    rw [lintegral_indicator_one (hTm B), measure_toMeasurable]
    exact hE B (Finset.mem_powerset.1 hB)
  rw [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul] at hsum
  have h2 := hint.trans (mul_le_mul_right hsum 2)
  push_cast at h2
  have hpow0 : (2 : ENNReal) ^ L.card ≠ 0 := pow_ne_zero _ two_ne_zero
  have hpowtop : (2 : ENNReal) ^ L.card ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofNat_ne_top
  rw [mul_left_comm] at h2
  exact (ENNReal.mul_le_mul_iff_right hpow0 hpowtop).1 h2

end Core

end RealizableLowerAux

open RealizableLowerAux

theorem solution :
    ∃ C₁ ε₀ δ₀ : ℝ, 0 < C₁ ∧ 0 < ε₀ ∧ 0 < δ₀ ∧
      ∀ {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSingletonClass X]
        [MeasurableSpace Y] [MeasurableSingletonClass Y] [Fintype Y]
        (H : Set (X → Y)) (d : ℕ), (∀ h ∈ H, Measurable h) → ndim H = d → 2 ≤ d →
        ∀ (A : Learner (X × Y) (X → Y)) (mH : ℝ → ℝ → ℕ), IsMulticlassPACWith H A mH →
          ∀ ε δ : ℝ, 0 < ε → ε < ε₀ → 0 < δ → δ < δ₀ →
            C₁ * (d + Real.log (1 / δ)) / ε ≤ mH ε δ := by
  refine ⟨1 / 96, 1 / 16, 1 / 4, by norm_num, by norm_num, by norm_num, ?_⟩
  intro X Y _ _ _ _ _ H d hmeas hdim hd A mH hA ε δ hε hε0 hδ hδ0
  classical
  obtain ⟨C, ⟨f₀, f₁, hf, hsh⟩, hC⟩ := exists_nshatters_card H d hdim (by omega)
  obtain ⟨a, haC⟩ : C.Nonempty := Finset.card_pos.mp (by omega)
  set L := C.erase a with hLdef
  have ha : a ∉ L := Finset.notMem_erase a C
  have hLcard : L.card = d - 1 := by rw [Finset.card_erase_of_mem haC, hC]
  have hL : L.Nonempty := Finset.card_pos.mp (by omega)
  have hins : insert a L = C := Finset.insert_erase haC
  have hLC : L ⊆ C := Finset.erase_subset a C
  have key : ∀ B ⊆ L, ∃ h ∈ H, (∀ x ∈ insert a B, h x = f₀ x) ∧
      ∀ x ∈ C, x ∉ insert a B → h x = f₁ x := fun B hB ↦
    hsh (insert a B) (Finset.insert_subset haC (hB.trans hLC))
  have : Nonempty (X → Y) := ⟨f₀⟩
  choose! t htH ht0 ht1 using key
  have ht_a : ∀ B ⊆ L, t B a = f₀ a := fun B hB ↦ ht0 B hB a (Finset.mem_insert_self a B)
  have ht_in : ∀ B ⊆ L, ∀ x ∈ B, t B x = f₀ x := fun B hB x hx ↦
    ht0 B hB x (Finset.mem_insert_of_mem hx)
  have ht_out : ∀ B ⊆ L, ∀ x ∈ L, x ∉ B → t B x = f₁ x := by
    intro B hB x hx hxB
    refine ht1 B hB x (hLC hx) ?_
    rw [Finset.mem_insert, not_or]
    exact ⟨Finset.ne_of_mem_erase hx, hxB⟩
  have hfL : ∀ x ∈ L, f₀ x ≠ f₁ x := fun x hx ↦ hf x (hLC hx)
  have htm : ∀ B ⊆ L, Measurable (t B) := fun B hB ↦ hmeas _ (htH B hB)
  have hε8 : 8 * ε ≤ 1 / 2 := by linarith
  set D := lbDist a L (8 * ε) with hD
  have hDprob : IsProbabilityMeasure D := lbDist_isProb hL (by linarith) (by linarith)
  set m := mH ε δ with hm
  have hPAC : ∀ B ⊆ L, iidLaw (D.map (fun x ↦ (x, t B x))) m
      {S | ENNReal.ofReal ε < D {x | A m S x ≠ t B x}} ≤ ENNReal.ofReal δ := fun B hB ↦
    hA ε δ hε (by linarith) hδ (by linarith) D hDprob (t B) (htm B hB)
      ⟨t B, htH B hB, by simp⟩ m le_rfl
  have hgood := measure_good_le A m hε (by linarith) hL hfL ht_a ht_in ht_out htm hPAC
  set μ := iidLaw D m with hμ
  have : IsProbabilityMeasure μ := by rw [hμ, iidLaw]; infer_instance
  -- (a) the all-heavy event
  have hA1 : (1 - 8 * ε) ^ m ≤ 2 * δ := by
    have h := hgood (Set.univ.pi fun _ ↦ {a})
      (MeasurableSet.univ_pi fun _ ↦ measurableSet_singleton a) (by
        intro xs hxs
        simp only [Set.mem_pi, Set.mem_univ, Set.mem_singleton_iff, true_implies] at hxs
        refine ⟨fun j ↦ by rw [hxs j]; exact Finset.mem_insert_self a L, ?_⟩
        have : unseen L xs = L := by
          simp only [unseen]
          exact Finset.filter_true_of_mem fun c hc j ↦ by
            rw [hxs j]; exact fun h ↦ ha (h ▸ hc)
        rw [this]; omega)
    rw [hμ, iidLaw, Measure.pi_pi] at h
    simp only [hD, lbDist_heavy ha, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
    rw [← ENNReal.ofReal_pow (by linarith), ← ENNReal.ofReal_ofNat 2,
      ← ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_le_ofReal_iff (by positivity)] at h
    exact h
  -- (b) the event that few light points are drawn
  have hB1 : ((d : ℝ) - 1) ≤ 32 * ε * m := by
    by_contra hlt
    rw [not_le] at hlt
    have hn : (L.card : ℝ) = d - 1 := by
      rw [hLcard]; push_cast [Nat.cast_sub (by omega : 1 ≤ d)]; ring
    set cnt : (Fin m → X) → ENNReal :=
      fun xs ↦ ∑ j, ((Function.eval j : (Fin m → X) → X) ⁻¹' ({a}ᶜ : Set X)).indicator 1 xs with hcnt
    have hne : MeasurableSet ({a}ᶜ : Set X) := (measurableSet_singleton a).compl
    have hmeas_j : ∀ j : Fin m, MeasurableSet ((Function.eval j : (Fin m → X) → X) ⁻¹' ({a}ᶜ : Set X)) :=
      fun j ↦ hne.preimage (measurable_pi_apply j)
    have hcntm : Measurable cnt :=
      Finset.measurable_sum _ fun j _ ↦ measurable_one.indicator (hmeas_j j)
    have hcnt_eq : ∀ xs, cnt xs =
        (((Finset.univ : Finset (Fin m)).filter (fun j ↦ xs j ≠ a)).card : ENNReal) := by
      intro xs
      rw [hcnt, Finset.natCast_card_filter]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      by_cases h : xs j = a <;> simp [h]
    have hint : ∫⁻ xs, cnt xs ∂μ = m * ENNReal.ofReal (8 * ε) := by
      rw [hcnt, lintegral_finsetSum _ (fun j _ ↦ measurable_one.indicator (hmeas_j j))]
      have : ∀ j : Fin m, ∫⁻ xs, ((Function.eval j : (Fin m → X) → X) ⁻¹' ({a}ᶜ : Set X)).indicator 1 xs ∂μ =
          ENNReal.ofReal (8 * ε) := by
        intro j
        rw [lintegral_indicator_one (hmeas_j j), hμ, iidLaw,
          (measurePreserving_eval (fun _ : Fin m ↦ D) j).measure_preimage
            hne.nullMeasurableSet, hD,
          lbDist_light ha hL]
      simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    set q : ENNReal := ENNReal.ofReal ((L.card : ℝ) / 2) with hq
    have hq0 : q ≠ 0 := by
      rw [hq]; simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      have : (0 : ℝ) < L.card := by exact_mod_cast hL.card_pos
      linarith
    set Bad : Set (Fin m → X) := {xs | q ≤ cnt xs} with hBad
    set Gin : Set (Fin m → X) := ⋂ j, (Function.eval j : (Fin m → X) → X) ⁻¹' ((insert a L : Finset X) : Set X)
      with hGin
    have hGinm : MeasurableSet Gin :=
      MeasurableSet.iInter fun j ↦ (Finset.measurableSet _).preimage (measurable_pi_apply j)
    have hBadm : MeasurableSet Bad := measurableSet_le measurable_const hcntm
    have hGinc : μ Ginᶜ = 0 := by
      rw [hGin, Set.compl_iInter]
      refine measure_iUnion_null fun j ↦ ?_
      rw [← Set.preimage_compl]
      exact Measure.pi_eval_preimage_null (fun _ : Fin m ↦ D) (lbDist_outside a L (8 * ε))
    have hMarkov : q * μ Bad ≤ m * ENNReal.ofReal (8 * ε) := by
      rw [← hint]; exact mul_meas_ge_le_lintegral₀ hcntm.aemeasurable q
    have hBad12 : μ Bad ≤ ENNReal.ofReal (1 / 2) := by
      have h1 : (m : ENNReal) * ENNReal.ofReal (8 * ε) ≤ q * ENNReal.ofReal (1 / 2) := by
        rw [hq, ← ENNReal.ofReal_mul (by positivity),
          show (m : ENNReal) = ENNReal.ofReal m by rw [ENNReal.ofReal_natCast],
          ← ENNReal.ofReal_mul (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        rw [hn]; nlinarith
      exact (ENNReal.mul_le_mul_iff_right hq0 ENNReal.ofReal_ne_top).1 (hMarkov.trans h1)
    have hGood := hgood (Gin \ Bad) (hGinm.diff hBadm) (by
      intro xs ⟨hin, hnb⟩
      have hin' : ∀ j, xs j ∈ insert a L := fun j ↦ by
        simpa using Set.mem_iInter.mp hin j
      refine ⟨hin', ?_⟩
      have hlt' : cnt xs < q := lt_of_not_ge hnb
      rw [hcnt_eq, hq, ← ENNReal.ofReal_natCast,
        ENNReal.ofReal_lt_ofReal_iff (by
          have : (0 : ℝ) < L.card := by exact_mod_cast hL.card_pos
          linarith)] at hlt'
      set k := ((Finset.univ : Finset (Fin m)).filter (fun j ↦ xs j ≠ a)).card with hk
      have hk2 : 2 * k < L.card := by
        have : (2 * k : ℝ) < L.card := by linarith
        exact_mod_cast this
      have hseen : (L.filter (fun c ↦ ¬ ∀ j, xs j ≠ c)).card ≤ k := by
        have : L.filter (fun c ↦ ¬ ∀ j, xs j ≠ c) ⊆
            ((Finset.univ : Finset (Fin m)).filter (fun j ↦ xs j ≠ a)).image xs := by
          intro c hc
          simp only [Finset.mem_filter, not_forall, not_not] at hc
          obtain ⟨hcL, j, hj⟩ := hc
          exact Finset.mem_image.2 ⟨j, by simp [hj]; exact fun h ↦ ha (h ▸ hcL), hj⟩
        exact (Finset.card_le_card this).trans Finset.card_image_le
      have hsplit := Finset.card_filter_add_card_filter_not (s := L) (fun c ↦ ∀ j, xs j ≠ c)
      have : (unseen L xs).card = (L.filter (fun c ↦ ∀ j, xs j ≠ c)).card := by
        simp only [unseen]
      omega)
    have hone : (1 : ENNReal) ≤ ENNReal.ofReal (2 * δ + 1 / 2) := by
      calc (1 : ENNReal) = μ Set.univ := measure_univ.symm
        _ ≤ μ (Gin \ Bad) + μ Ginᶜ + μ Bad := by
          refine (measure_mono (fun xs _ ↦ ?_)).trans
            ((measure_union_le _ _).trans (by gcongr; exact measure_union_le _ _))
          by_cases h1 : xs ∈ Gin
          · by_cases h2 : xs ∈ Bad
            · exact Or.inr h2
            · exact Or.inl (Or.inl ⟨h1, h2⟩)
          · exact Or.inl (Or.inr h1)
        _ ≤ 2 * ENNReal.ofReal δ + 0 + ENNReal.ofReal (1 / 2) := by
          rw [hGinc]; gcongr
        _ = ENNReal.ofReal (2 * δ + 1 / 2) := by
          rw [add_zero, ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num),
            ← ENNReal.ofReal_add (by positivity) (by norm_num)]
    rw [← ENNReal.ofReal_one, ENNReal.ofReal_le_ofReal_iff (by positivity)] at hone
    linarith
  -- arithmetic
  have hlog : Real.log (1 / δ) ≤ 32 * ε * m := by
    have hpos : 0 < 1 - 8 * ε := by linarith
    have h1 : (m : ℝ) * Real.log (1 - 8 * ε) ≤ Real.log (2 * δ) := by
      rw [← Real.log_pow]
      exact Real.log_le_log (pow_pos hpos m) hA1
    have h2 : -(16 * ε) ≤ Real.log (1 - 8 * ε) := by
      have := Real.one_sub_inv_le_log_of_pos hpos
      have h3 : -(16 * ε) ≤ 1 - (1 - 8 * ε)⁻¹ := by
        have e : 1 - (1 - 8 * ε)⁻¹ = -(8 * ε / (1 - 8 * ε)) := by
          field_simp; ring
        rw [e, neg_le_neg_iff, div_le_iff₀ hpos]
        nlinarith
      linarith
    have h4 : Real.log (2 * δ) = Real.log 2 - Real.log (1 / δ) := by
      rw [Real.log_mul (by norm_num) hδ.ne', one_div, Real.log_inv]; ring
    have h5 : 2 * Real.log 2 ≤ Real.log (1 / δ) := by
      rw [← Real.log_rpow (by norm_num)]
      apply Real.log_le_log (by positivity)
      rw [le_div_iff₀ hδ]; norm_num; linarith
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
    nlinarith
  have hdle : (d : ℝ) ≤ 64 * ε * m := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  rw [div_le_iff₀ hε]
  nlinarith
