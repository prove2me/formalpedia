-- Prove2me | solution 1 for SupportVectorMachines.Calibration.lemma_3_4_bayes_risk_via_inner_risk_v2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T07:18:47.724981+00:00
-- url     : https://prove2.me/submissions/65e1f1be-20e4-4d11-8ab5-369f66391a32

import Mathlib
import Definitions.Def_SupportVectorMachines_Calibration_Loss_v2
import Definitions.Def_SupportVectorMachines_Calibration_InnerRisks_v2
import Definitions.Def_SupportVectorMachines_Calibration_OuterRisks_v2
import Definitions.Def_SupportVectorMachines_Calibration_IsCompleteMeasurableSpace_v2

open MeasureTheory
open Set Filter Topology ENNReal

namespace SupportVectorMachines.Calibration

universe u
class IsBorelSpace (X : Type u) [TopologicalSpace X] : Prop where
  exists_homeomorph_borel :
    ∃ (Z : Type u) (_ : MetricSpace Z) (_ : CompleteSpace Z)
      (_ : TopologicalSpace.SeparableSpace Z) (B : Set Z),
      MeasurableSet[borel Z] B ∧ Nonempty (X ≃ₜ B)

def IsUniversallyMeasurable {X : Type*} [MeasurableSpace X] (E : Set X) : Prop :=
  ∀ p : Measure X, IsProbabilityMeasure p → NullMeasurableSet E p

set_option warn.classDefReducibility false in
def analyticSigmaAlgebra (X : Type*) [TopologicalSpace X] : MeasurableSpace X :=
  MeasurableSpace.generateFrom {A : Set X | AnalyticSet A}

def IsAnalyticallyMeasurable {X : Type*} [TopologicalSpace X] (E : Set X) : Prop :=
  MeasurableSet[analyticSigmaAlgebra X] E

def IsAnalyticallyMeasurableFun {X Y : Type*} [TopologicalSpace X] [MeasurableSpace Y]
    (D : Set X) (f : D → Y) : Prop :=
  IsAnalyticallyMeasurable D ∧
    ∀ B : Set Y, MeasurableSet B → IsAnalyticallyMeasurable (Subtype.val '' (f ⁻¹' B))

lemma au_cyl_of_nhds {σ : ℕ → ℕ} {U : Set (ℕ → ℕ)} (hU : U ∈ 𝓝 σ) :
    ∃ m, ∀ τ : ℕ → ℕ, (∀ i < m, τ i = σ i) → τ ∈ U := by
  rw [nhds_pi, Filter.mem_pi] at hU
  obtain ⟨I, hI, t, ht, hsub⟩ := hU
  obtain ⟨m, hm⟩ := hI.bddAbove
  refine ⟨m+1, fun τ hτ => hsub ?_⟩
  intro i hi
  have : τ i = σ i := hτ i (Nat.lt_succ_of_le (hm hi))
  rw [this]; exact mem_of_mem_nhds (ht i)

lemma au_Kinf_compact (b : ℕ → ℕ) : IsCompact {σ : ℕ → ℕ | ∀ i, σ i ≤ b i} := by
  have : {σ : ℕ → ℕ | ∀ i, σ i ≤ b i} = Set.pi univ (fun i => Iic (b i)) := by ext; simp [Pi.le_def]
  rw [this]; exact isCompact_univ_pi (fun i => (Set.finite_Iic _).isCompact)

lemma au_cyl_open (σ : ℕ → ℕ) (n : ℕ) : IsOpen {τ : ℕ → ℕ | ∀ i < n, τ i = σ i} := by
  have : {τ : ℕ → ℕ | ∀ i < n, τ i = σ i} = (Iio n).pi (fun i => {σ i}) := by
    ext τ; simp [Set.mem_pi]
  rw [this]; exact isOpen_set_pi (Set.finite_Iio n) (fun i _ => isOpen_discrete _)

lemma au_eventually_sub (b : ℕ → ℕ) {U : Set (ℕ → ℕ)} (hU : IsOpen U)
    (hK : {σ : ℕ → ℕ | ∀ i, σ i ≤ b i} ⊆ U) :
    ∃ k, {σ : ℕ → ℕ | ∀ i < k, σ i ≤ b i} ⊆ U := by
  have key : ∀ σ ∈ {σ : ℕ → ℕ | ∀ i, σ i ≤ b i},
      ∃ m, ∀ τ : ℕ → ℕ, (∀ i < m, τ i = σ i) → τ ∈ U :=
    fun σ hσ => au_cyl_of_nhds (hU.mem_nhds (hK hσ))
  choose! m hm using key
  obtain ⟨F, hFK, hF, hcover⟩ := (au_Kinf_compact b).elim_finite_subcover_image
    (b := {σ : ℕ → ℕ | ∀ i, σ i ≤ b i})
    (c := fun σ => {τ : ℕ → ℕ | ∀ i < m σ, τ i = σ i})
    (fun σ _ => au_cyl_open σ (m σ))
    (fun σ hσ => mem_biUnion hσ (fun i _ => rfl))
  obtain ⟨k, hk⟩ := (hF.image m).bddAbove
  refine ⟨k, fun ρ hρ => ?_⟩
  let ρ' : ℕ → ℕ := fun i => if i < k then ρ i else 0
  have hρ' : ρ' ∈ {σ : ℕ → ℕ | ∀ i, σ i ≤ b i} := by
    intro i
    by_cases hi : i < k
    · simp only [ρ', if_pos hi]; exact hρ i hi
    · simp only [ρ', if_neg hi]; exact Nat.zero_le _
  have := hcover hρ'
  simp only [mem_iUnion, mem_setOf_eq] at this
  obtain ⟨σ, hσF, hagree⟩ := this
  have hmk : m σ ≤ k := hk (mem_image_of_mem m hσF)
  apply hm σ (hFK hσF) ρ
  intro i hi
  have h1 := hagree i hi
  have hik : i < k := lt_of_lt_of_le hi hmk
  simp only [ρ', if_pos hik] at h1
  exact h1

noncomputable def auSeqB (g : (ℕ → ℕ) → ℕ → ℕ) : ℕ → (ℕ → ℕ)
  | 0 => 0
  | k+1 => Function.update (auSeqB g k) k (g (auSeqB g k) k)

lemma auSeqB_agree (g : (ℕ → ℕ) → ℕ → ℕ) :
    ∀ n i, i < n → auSeqB g n i = auSeqB g (i+1) i := by
  intro n
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
    intro i hi
    by_cases h : i = n
    · subst h; rfl
    · have hin : i < n := by omega
      show Function.update (auSeqB g n) n (g (auSeqB g n) n) i = _
      rw [Function.update_of_ne h]
      exact ih i hin

lemma au_analytic_inner {X : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ] (f : (ℕ → ℕ) → X)
    (hf : Continuous f) (ε : ℝ≥0∞) (hε : ε ≠ 0) :
    ∃ C : Set X, MeasurableSet C ∧ C ⊆ range f ∧ μ (range f) ≤ μ C + ε := by
  obtain ⟨δ, hδpos, hδsum⟩ := ENNReal.exists_pos_sum_of_countable hε ℕ
  let Kk : (ℕ → ℕ) → ℕ → Set (ℕ → ℕ) := fun b k => {σ | ∀ i < k, σ i ≤ b i}
  have step : ∀ b k, ∃ m, μ (f '' Kk b k) ≤
      μ (f '' Kk (Function.update b k m) (k+1)) + δ k := by
    intro b k
    have hU : Kk b k = ⋃ m, Kk (Function.update b k m) (k+1) := by
      ext σ
      simp only [Kk, mem_setOf_eq, mem_iUnion]
      constructor
      · intro h
        refine ⟨σ k, fun i hi => ?_⟩
        by_cases hik : i = k
        · subst hik; simp
        · rw [Function.update_of_ne hik]; exact h i (by omega)
      · rintro ⟨m, h⟩ i hi
        have := h i (by omega)
        rwa [Function.update_of_ne (by omega)] at this
    have hmono : Monotone (fun m => f '' Kk (Function.update b k m) (k+1)) := by
      intro m m' hmm' τ hτ
      obtain ⟨σ, hσ, rfl⟩ := hτ
      refine ⟨σ, fun i hi => ?_, rfl⟩
      have := hσ i hi
      by_cases hik : i = k
      · subst hik; simp only [Function.update_self] at this ⊢; omega
      · rwa [Function.update_of_ne hik] at this ⊢
    have hS : μ (f '' Kk b k) = ⨆ m, μ (f '' Kk (Function.update b k m) (k+1)) := by
      rw [hU, image_iUnion]; exact hmono.measure_iUnion
    set S := μ (f '' Kk b k) with hSdef
    by_cases hS0 : S = 0
    · exact ⟨0, by rw [hS0]; exact bot_le⟩
    have hlt : S - δ k < S :=
      ENNReal.sub_lt_self (measure_ne_top _ _) hS0 (by simpa using (hδpos k).ne')
    rw [hS] at hlt
    obtain ⟨m, hm⟩ := lt_iSup_iff.1 hlt
    refine ⟨m, ?_⟩
    rw [hS]
    exact (tsub_le_iff_right).1 hm.le |>.trans_eq' (by rw [← hS])
  choose g hg using step
  let B := auSeqB g
  let b : ℕ → ℕ := fun i => B (i+1) i
  have hKB : ∀ k, Kk (B k) k = Kk b k := by
    intro k; ext σ
    simp only [Kk, mem_setOf_eq]
    constructor
    · intro h i hi; exact le_of_le_of_eq (h i hi) (auSeqB_agree g k i hi)
    · intro h i hi; exact le_of_le_of_eq (h i hi) (auSeqB_agree g k i hi).symm
  have tele : ∀ k, μ (range f) ≤ μ (f '' Kk b k) + ∑ i ∈ Finset.range k, (δ i : ℝ≥0∞) := by
    intro k
    induction k with
    | zero =>
      have : Kk b 0 = univ := by ext σ; simp [Kk]
      simp [this, image_univ]
    | succ k ih =>
      refine ih.trans ?_
      rw [Finset.sum_range_succ, ← hKB k]
      have := hg (B k) k
      have hBk : B (k+1) = Function.update (B k) k (g (B k) k) := rfl
      rw [← hBk, hKB (k+1)] at this
      calc μ (f '' Kk (B k) k) + ∑ i ∈ Finset.range k, (δ i : ℝ≥0∞)
          ≤ (μ (f '' Kk b (k+1)) + δ k) + ∑ i ∈ Finset.range k, (δ i : ℝ≥0∞) :=
            add_le_add this le_rfl
        _ = _ := by ring
  have hsumle : ∀ k, ∑ i ∈ Finset.range k, (δ i : ℝ≥0∞) ≤ ε :=
    fun k => (ENNReal.sum_le_tsum _).trans hδsum.le
  refine ⟨⋂ k, closure (f '' Kk b k), MeasurableSet.iInter
    (fun k => isClosed_closure.measurableSet), ?_, ?_⟩
  · -- inclusion
    intro y hy
    by_contra hyA
    have hKc := au_Kinf_compact b
    have hyK : y ∉ f '' {σ : ℕ → ℕ | ∀ i, σ i ≤ b i} := fun h => hyA (image_subset_range _ _ h)
    obtain ⟨U, V, hUo, hVo, hyU, hKV, hUV⟩ :=
      SeparatedNhds.of_isCompact_isCompact isCompact_singleton (hKc.image hf)
        (disjoint_singleton_left.2 hyK)
    obtain ⟨k, hk⟩ := au_eventually_sub b (hVo.preimage hf)
      (fun σ hσ => hKV (mem_image_of_mem f hσ))
    have h1 : f '' Kk b k ⊆ V := by
      rintro _ ⟨σ, hσ, rfl⟩; exact hk hσ
    have hd : Disjoint U (closure (f '' Kk b k)) :=
      (hUV.mono_right h1).closure_right hUo
    have hyc : y ∈ closure (f '' Kk b k) := mem_iInter.1 hy k
    exact hd.ne_of_mem (hyU rfl) hyc rfl
  · have hanti : Antitone (fun k => closure (f '' Kk b k)) := by
      intro k k' hkk'
      apply closure_mono
      rintro _ ⟨σ, hσ, rfl⟩
      exact ⟨σ, fun i hi => hσ i (lt_of_lt_of_le hi hkk'), rfl⟩
    rw [hanti.measure_iInter (fun k => isClosed_closure.measurableSet.nullMeasurableSet)
      ⟨0, measure_ne_top _ _⟩, ENNReal.iInf_add]
    refine le_iInf fun k => ?_
    exact (tele k).trans (add_le_add (measure_mono subset_closure) (hsumle k))

lemma au_null_of_inner {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (A : Set X)
    (h : ∀ ε : ℝ≥0∞, ε ≠ 0 → ∃ C, MeasurableSet C ∧ C ⊆ A ∧ μ A ≤ μ C + ε) :
    NullMeasurableSet A μ := by
  have h' : ∀ n : ℕ, ∃ C, MeasurableSet C ∧ C ⊆ A ∧ μ A ≤ μ C + (n : ℝ≥0∞)⁻¹ :=
    fun n => h _ (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top n))
  choose C hCm hCA hCμ using h'
  let S := ⋃ n, C n
  have hSm : MeasurableSet S := MeasurableSet.iUnion hCm
  have hSA : S ⊆ A := iUnion_subset hCA
  have hle : μ A ≤ μ S := by
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt (a := (ε : ℝ≥0∞)) (by simpa using hε.ne')
    calc μ A ≤ μ (C n) + (n : ℝ≥0∞)⁻¹ := hCμ n
      _ ≤ μ S + ε := add_le_add (measure_mono (subset_iUnion C n)) hn.le
  have h0 : μ (A \ S) = 0 := by
    have hT : μ (toMeasurable μ A \ S) = 0 := by
      rw [measure_diff ((subset_toMeasurable μ A).trans' hSA |> fun h => h)
        hSm.nullMeasurableSet (measure_ne_top _ _), measure_toMeasurable]
      exact tsub_eq_zero_of_le hle
    exact measure_mono_null (diff_subset_diff_left (subset_toMeasurable μ A)) hT
  have : A = S ∪ (A \ S) := (union_diff_cancel hSA).symm
  rw [this]
  exact hSm.nullMeasurableSet.union (NullMeasurableSet.of_null h0)

lemma au_t2 {X : Type*} [TopologicalSpace X] [IsBorelSpace X] : T2Space X := by
  obtain ⟨Z, _, _, _, B, _, ⟨e⟩⟩ := IsBorelSpace.exists_homeomorph_borel (X := X)
  exact e.isEmbedding.t2Space

theorem analytic_universallyMeasurable_core {X : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [IsBorelSpace X]
    (A : Set X) (hA : AnalyticSet A) : IsUniversallyMeasurable A := by
  have := au_t2 (X := X)
  intro p hp
  rw [AnalyticSet] at hA
  rcases hA with hA | ⟨f, hf, rfl⟩
  · subst hA; exact nullMeasurableSet_empty
  · exact au_null_of_inner p _ (fun ε hε => au_analytic_inner p f hf ε hε)


lemma cm_second {X : Type*} [TopologicalSpace X] [IsBorelSpace X] : SecondCountableTopology X := by
  obtain ⟨Z, _, _, _, B, _, ⟨e⟩⟩ := IsBorelSpace.exists_homeomorph_borel (X := X)
  exact e.isEmbedding.secondCountableTopology

lemma cm_am_um {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [IsBorelSpace X] (E : Set X) (hE : IsAnalyticallyMeasurable E) :
    IsUniversallyMeasurable E := by
  intro p hp
  exact MeasurableSpace.generateFrom_induction _ (fun s _ => NullMeasurableSet s p)
    (fun t ht _ => analytic_universallyMeasurable_core t ht p hp) nullMeasurableSet_empty
    (fun t _ h => h.compl) (fun s _ h => NullMeasurableSet.iUnion h) E hE


noncomputable def jvSeq (P : (ℕ → ℕ) → ℕ → Prop) : ℕ → (ℕ → ℕ)
  | 0 => 0
  | k+1 => Function.update (jvSeq P k) k (sInf {n | P (Function.update (jvSeq P k) k n) (k+1)})

lemma jvSeq_agree (P : (ℕ → ℕ) → ℕ → Prop) :
    ∀ n i, i < n → jvSeq P n i = jvSeq P (i+1) i := by
  intro n
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
    intro i hi
    by_cases h : i = n
    · subst h; rfl
    · have hin : i < n := by omega
      show Function.update (jvSeq P n) n _ i = _
      rw [Function.update_of_ne h]
      exact ih i hin

section JV
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (G : (ℕ → ℕ) → X × Y)

def jvCyl (t : ℕ → ℕ) (k : ℕ) : Set (ℕ → ℕ) := {σ | ∀ i < k, σ i = t i}
def jvW (t : ℕ → ℕ) (k : ℕ) : Set X := (fun σ => (G σ).1) '' jvCyl t k
noncomputable def jvT (x : X) : ℕ → (ℕ → ℕ) := jvSeq (fun t k => x ∈ jvW G t k)
noncomputable def jvS (x : X) : ℕ → ℕ := fun i => jvT G x (i+1) i
def jvQ (k : ℕ) (t : ℕ → ℕ) : Set X :=
  (Prod.fst '' range G) ∩ {x | ∀ j < k, jvT G x k j = t j}
def jvExt (i : ℕ) (u : Fin (i+1) → ℕ) : ℕ → ℕ := fun j => if h : j < i+1 then u ⟨j, h⟩ else 0

lemma jvW_congr {t t' : ℕ → ℕ} {k : ℕ} (h : ∀ i < k, t i = t' i) :
    jvW G t k = jvW G t' k := by
  unfold jvW jvCyl
  congr 1
  ext σ
  simp only [mem_setOf_eq]
  constructor <;> intro hσ i hi
  · rw [hσ i hi, h i hi]
  · rw [hσ i hi, ← h i hi]

lemma jvW_zero (t : ℕ → ℕ) : jvW G t 0 = Prod.fst '' range G := by
  unfold jvW jvCyl
  ext x; simp

lemma jvT_mem (x : X) (hx : x ∈ Prod.fst '' range G) : ∀ k, x ∈ jvW G (jvT G x k) k := by
  intro k
  induction k with
  | zero => rw [jvW_zero]; exact hx
  | succ k ih =>
    obtain ⟨σ, hσ, hσx⟩ := ih
    have hne : σ k ∈ {n | x ∈ jvW G (Function.update (jvT G x k) k n) (k+1)} := by
      refine ⟨σ, fun i hi => ?_, hσx⟩
      by_cases hik : i = k
      · subst hik; simp
      · rw [Function.update_of_ne hik]; exact hσ i (by omega)
    exact Nat.sInf_mem ⟨_, hne⟩

lemma jvS_mem [T2Space X] (hG : Continuous G) (x : X) (hx : x ∈ Prod.fst '' range G) :
    (G (jvS G x)).1 = x := by
  have hcl : IsClosed {σ : ℕ → ℕ | (G σ).1 = x} :=
    isClosed_singleton.preimage (continuous_fst.comp hG)
  have : jvS G x ∈ closure {σ : ℕ → ℕ | (G σ).1 = x} := by
    rw [mem_closure_iff_nhds]
    intro U hU
    obtain ⟨m, hm⟩ := au_cyl_of_nhds hU
    obtain ⟨σ, hσ, hσx⟩ := jvT_mem G x hx m
    refine ⟨σ, hm σ (fun i hi => ?_), hσx⟩
    rw [hσ i hi]; exact jvSeq_agree _ m i hi
  rw [hcl.closure_eq] at this; exact this

lemma jv_set_eq (x : X) (k : ℕ) (t : ℕ → ℕ) (hk : ∀ j < k, jvT G x k j = t j) :
    {n | x ∈ jvW G (Function.update (jvT G x k) k n) (k+1)} =
      {n | x ∈ jvW G (Function.update t k n) (k+1)} := by
  ext n
  simp only [mem_setOf_eq]
  rw [jvW_congr G (t' := Function.update t k n) (fun i hi => ?_)]
  by_cases hik : i = k
  · subst hik; simp
  · rw [Function.update_of_ne hik, Function.update_of_ne hik]; exact hk i (by omega)

lemma jvQ_succ (k : ℕ) (t : ℕ → ℕ) :
    jvQ G (k+1) t = jvQ G k t ∩ jvW G t (k+1) ∩
      ⋂ j ∈ Iio (t k), (jvW G (Function.update t k j) (k+1))ᶜ := by
  ext x
  simp only [jvQ, mem_inter_iff, mem_setOf_eq, mem_iInter, mem_Iio, mem_compl_iff]
  have hsucc : jvT G x (k+1) = Function.update (jvT G x k) k
      (sInf {n | x ∈ jvW G (Function.update (jvT G x k) k n) (k+1)}) := rfl
  constructor
  · rintro ⟨hx, h⟩
    have hk : ∀ j < k, jvT G x k j = t j := fun j hj => by
      have := h j (by omega); rwa [hsucc, Function.update_of_ne (by omega)] at this
    have hm := h k (by omega)
    rw [hsucc, Function.update_self, jv_set_eq G x k t hk] at hm
    refine ⟨⟨⟨hx, hk⟩, ?_⟩, fun j hj => ?_⟩
    · have := jvT_mem G x hx (k+1)
      rwa [jvW_congr G h] at this
    · exact Nat.notMem_of_lt_sInf (hm ▸ hj)
  · rintro ⟨⟨⟨hx, hk⟩, hW⟩, hlt⟩
    refine ⟨hx, fun j hj => ?_⟩
    rw [hsucc, jv_set_eq G x k t hk]
    have hmem : t k ∈ {n | x ∈ jvW G (Function.update t k n) (k+1)} := by
      simp only [mem_setOf_eq, Function.update_eq_self]; exact hW
    have hinf : sInf {n | x ∈ jvW G (Function.update t k n) (k+1)} = t k := by
      refine le_antisymm (Nat.sInf_le hmem) ?_
      by_contra hcon
      push_neg at hcon
      exact hlt _ hcon (Nat.sInf_mem ⟨_, hmem⟩)
    by_cases hjk : j = k
    · subst hjk; rw [Function.update_self, hinf]
    · rw [Function.update_of_ne hjk]; exact hk j (by omega)

lemma jvW_am (hG : Continuous G) (t : ℕ → ℕ) (k : ℕ) :
    MeasurableSet[analyticSigmaAlgebra X] (jvW G t k) :=
  MeasurableSpace.measurableSet_generateFrom
    ((au_cyl_open t k).analyticSet_image (continuous_fst.comp hG))

lemma jvQ_am (hG : Continuous G) : ∀ k t, MeasurableSet[analyticSigmaAlgebra X] (jvQ G k t) := by
  intro k
  induction k with
  | zero =>
    intro t
    have : jvQ G 0 t = jvW G t 0 := by
      rw [jvW_zero]; ext x; simp [jvQ]
    rw [this]; exact jvW_am G hG t 0
  | succ k ih =>
    intro t
    rw [jvQ_succ]
    exact MeasurableSet.inter (MeasurableSet.inter (ih t) (jvW_am G hG t (k+1)))
      (MeasurableSet.biInter (Set.to_countable _) fun j _ => (jvW_am G hG _ _).compl)

lemma jv_pre_am (hG : Continuous G) (C : Set (ℕ → ℕ)) (hC : MeasurableSet C) :
    MeasurableSet[analyticSigmaAlgebra X] ((Prod.fst '' range G) ∩ jvS G ⁻¹' C) := by
  have hC' : MeasurableSet[MeasurableSpace.generateFrom
      {B | ∃ (i : ℕ) (A : Set ℕ), MeasurableSet A ∧ Function.eval i ⁻¹' A = B}] C := by
    rw [← MeasurableSpace.pi_eq_generateFrom_projections]; exact hC
  have hP : MeasurableSet[analyticSigmaAlgebra X] (Prod.fst '' range G) := by
    rw [← jvW_zero G 0]; exact jvW_am G hG 0 0
  refine MeasurableSpace.generateFrom_induction _
    (fun C _ => MeasurableSet[analyticSigmaAlgebra X] ((Prod.fst '' range G) ∩ jvS G ⁻¹' C))
    ?_ ?_ ?_ ?_ C hC'
  · rintro _ ⟨i, T, -, rfl⟩ -
    have : (Prod.fst '' range G) ∩ jvS G ⁻¹' (Function.eval i ⁻¹' T) =
        ⋃ u ∈ {u : Fin (i+1) → ℕ | u (Fin.last i) ∈ T}, jvQ G (i+1) (jvExt i u) := by
      ext x
      simp only [mem_inter_iff, mem_preimage, Function.eval, mem_iUnion, mem_setOf_eq,
        exists_prop, jvQ]
      constructor
      · rintro ⟨hx, hT⟩
        refine ⟨fun j => jvS G x j, hT, hx, fun j hj => ?_⟩
        simp only [jvExt, dif_pos hj]
        exact jvSeq_agree _ (i+1) j hj
      · rintro ⟨u, hu, hx, hq⟩
        refine ⟨hx, ?_⟩
        have := hq i (Nat.lt_succ_self i)
        simp only [jvExt, dif_pos (Nat.lt_succ_self i)] at this
        show jvT G x (i+1) i ∈ T
        rw [this]; exact hu
    rw [this]
    exact MeasurableSet.biUnion (Set.to_countable _) (fun u _ => jvQ_am G hG _ _)
  · simp only [preimage_empty, inter_empty]; exact @MeasurableSet.empty X (analyticSigmaAlgebra X)
  · intro C _ h
    have : (Prod.fst '' range G) ∩ jvS G ⁻¹' Cᶜ =
        (Prod.fst '' range G) \ ((Prod.fst '' range G) ∩ jvS G ⁻¹' C) := by
      ext x; simp only [mem_inter_iff, mem_preimage, mem_compl_iff, mem_diff]; tauto
    rw [this]; exact MeasurableSet.inter hP (MeasurableSet.compl h)
  · intro C _ h
    rw [preimage_iUnion, inter_iUnion]; exact MeasurableSet.iUnion h

end JV

theorem jankov_von_neumann_core {X Y : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [IsBorelSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [IsBorelSpace Y]
    (A : Set (X × Y)) (hA : AnalyticSet A) :
    ∃ φ : (Prod.fst '' A) → Y,
      IsAnalyticallyMeasurableFun (Prod.fst '' A) φ ∧
        ∀ x : Prod.fst '' A, ((x : X), φ x) ∈ A := by
  classical
  have hT2 := au_t2 (X := X)
  have hpA : IsAnalyticallyMeasurable (Prod.fst '' A) :=
    MeasurableSpace.measurableSet_generateFrom (hA.image_of_continuous continuous_fst)
  rw [AnalyticSet] at hA
  rcases hA with hA | ⟨G, hG, rfl⟩
  · subst hA
    refine ⟨fun x => False.elim (by simpa using x.2), ⟨hpA, fun B _ => ?_⟩,
      fun x => False.elim (by simpa using x.2)⟩
    have h0 : ∀ s : Set (Prod.fst '' (∅ : Set (X × Y))), Subtype.val '' s = ∅ := by
      intro s; ext y; simp
    rw [h0]; exact @MeasurableSet.empty X (analyticSigmaAlgebra X)
  · refine ⟨fun x => (G (jvS G x)).2, ⟨hpA, fun B hB => ?_⟩,
      fun x => ⟨jvS G x, Prod.ext (jvS_mem G hG x x.2) rfl⟩⟩
    have hH : Measurable (fun σ : ℕ → ℕ => (G σ).2) := (continuous_snd.comp hG).measurable
    have : Subtype.val '' ((fun x : Prod.fst '' range G => (G (jvS G x)).2) ⁻¹' B) =
        (Prod.fst '' range G) ∩ jvS G ⁻¹' ((fun σ => (G σ).2) ⁻¹' B) := by
      ext x
      constructor
      · rintro ⟨x', hx', rfl⟩; exact ⟨x'.2, hx'⟩
      · rintro ⟨hx, hB⟩; exact ⟨⟨x, hx⟩, hB, rfl⟩
    rw [this]
    exact jv_pre_am G hG _ (hH hB)


instance polish_isBorelSpace (X : Type u) [TopologicalSpace X] [PolishSpace X] : IsBorelSpace X := by
  letI := TopologicalSpace.upgradeIsCompletelyMetrizable X
  refine ⟨⟨X, inferInstance, inferInstance, inferInstance, Set.univ, MeasurableSet.univ, ⟨?_⟩⟩⟩
  exact (Homeomorph.Set.univ X).symm

instance pi_bool_polish (ι : Type*) [Countable ι] : PolishSpace (ι → Bool) := by
  haveI : TopologicalSpace.SeparableSpace (ι → Bool) := inferInstance
  haveI : TopologicalSpace.IsCompletelyMetrizableSpace (ι → Bool) := inferInstance
  infer_instance

section Reduction
variable {X : Type*} [MeasurableSpace X]

open Classical in
noncomputable def codeMap (𝒰 : Set (Set X)) (x : X) : ↥𝒰 → Bool := fun u => decide (x ∈ (u : Set X))

lemma measurable_codeMap (𝒰 : Set (Set X)) (h : ∀ U ∈ 𝒰, MeasurableSet U) :
    Measurable (codeMap 𝒰) := by
  classical
  refine measurable_pi_iff.2 (fun u => ?_)
  refine measurable_to_bool ?_
  have : (fun x => codeMap 𝒰 x u) ⁻¹' {true} = (u : Set X) := by
    ext x; simp [codeMap]
  rw [this]
  exact h _ u.2

lemma exists_countable_rect (B : Set (X × ℝ)) (hB : MeasurableSet B) :
    ∃ 𝒰 : Set (Set X), 𝒰.Countable ∧ (∀ U ∈ 𝒰, MeasurableSet U) ∧
      MeasurableSet[MeasurableSpace.generateFrom
        (Set.image2 (· ×ˢ ·) 𝒰 {V : Set ℝ | MeasurableSet V})] B := by
  rw [← generateFrom_prod] at hB
  refine MeasurableSpace.generateFrom_induction _
    (fun s _ => ∃ 𝒰 : Set (Set X), 𝒰.Countable ∧ (∀ U ∈ 𝒰, MeasurableSet U) ∧
      MeasurableSet[MeasurableSpace.generateFrom
        (Set.image2 (· ×ˢ ·) 𝒰 {V : Set ℝ | MeasurableSet V})] s) ?_ ?_ ?_ ?_ B hB
  · rintro t ⟨U, hU, V, hV, rfl⟩ _
    refine ⟨{U}, Set.countable_singleton _, by simpa using hU, ?_⟩
    exact MeasurableSpace.measurableSet_generateFrom ⟨U, rfl, V, hV, rfl⟩
  · exact ⟨∅, Set.countable_empty, by simp, MeasurableSpace.measurableSet_empty _⟩
  · rintro t ht ⟨𝒰, h1, h2, h3⟩
    exact ⟨𝒰, h1, h2, h3.compl⟩
  · intro s hs ih
    choose 𝒰 h1 h2 h3 using ih
    refine ⟨⋃ n, 𝒰 n, Set.countable_iUnion h1, ?_, ?_⟩
    · intro U hU
      obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hU
      exact h2 n U hn
    · refine MeasurableSet.iUnion (fun n => ?_)
      refine MeasurableSpace.generateFrom_mono ?_ _ (h3 n)
      exact Set.image2_subset (Set.subset_iUnion _ n) subset_rfl

lemma exists_reduction (B : Set (X × ℝ)) (hB : MeasurableSet B) :
    ∃ 𝒰 : Set (Set X), 𝒰.Countable ∧ Measurable (codeMap 𝒰) ∧
      ∃ B' : Set ((↥𝒰 → Bool) × ℝ), MeasurableSet B' ∧
        B = (fun p : X × ℝ => (codeMap 𝒰 p.1, p.2)) ⁻¹' B' := by
  classical
  obtain ⟨𝒰, h1, h2, h3⟩ := exists_countable_rect B hB
  have hφ := measurable_codeMap 𝒰 h2
  have hle : MeasurableSpace.generateFrom
        (Set.image2 (· ×ˢ ·) 𝒰 {V : Set ℝ | MeasurableSet V}) ≤
      MeasurableSpace.comap (fun p : X × ℝ => (codeMap 𝒰 p.1, p.2)) inferInstance := by
    refine MeasurableSpace.generateFrom_le ?_
    rintro t ⟨U, hU, V, hV, rfl⟩
    refine ⟨{b | b ⟨U, hU⟩ = true} ×ˢ V, ?_, ?_⟩
    · refine MeasurableSet.prod ?_ hV
      exact (measurable_pi_apply (X := fun _ : ↥𝒰 => Bool) (⟨U, hU⟩ : ↥𝒰)) (MeasurableSet.of_discrete (s := {true}))
    · ext ⟨x, y⟩
      simp [codeMap]
  obtain ⟨B', hB', hB'eq⟩ := hle _ h3
  exact ⟨𝒰, h1, hφ, B', hB', hB'eq.symm⟩

end Reduction

section Projection
variable {X : Type*} [MeasurableSpace X]

lemma proj_nullMeasurable (μ : Measure X) [IsProbabilityMeasure μ] (B : Set (X × ℝ))
    (hB : MeasurableSet B) : NullMeasurableSet (Prod.fst '' B) μ := by
  obtain ⟨𝒰, hc, hφ, B', hB', rfl⟩ := exists_reduction B hB
  have : Countable ↥𝒰 := hc.to_subtype
  have hA : AnalyticSet (Prod.fst '' B') :=
    (hB'.analyticSet).image_of_continuous continuous_fst
  have hU : IsUniversallyMeasurable (Prod.fst '' B') := analytic_universallyMeasurable_core _ hA
  have hν : IsProbabilityMeasure (μ.map (codeMap 𝒰)) := ⟨by rw [Measure.map_apply hφ MeasurableSet.univ]; simp⟩
  have h1 := hU _ hν
  have h2 := h1.preimage (hφ.quasiMeasurePreserving μ)
  have : Prod.fst '' ((fun p : X × ℝ => (codeMap 𝒰 p.1, p.2)) ⁻¹' B') =
      codeMap 𝒰 ⁻¹' (Prod.fst '' B') := by
    ext x
    simp only [mem_image, mem_preimage, Prod.exists, exists_and_right, exists_eq_right]
  rw [this]; exact h2

lemma exists_measurable_section (μ : Measure X) [IsProbabilityMeasure μ] (B : Set (X × ℝ))
    (hB : MeasurableSet B) :
    ∃ f : X → ℝ, Measurable f ∧ ∀ᵐ x ∂μ, (∃ t, (x, t) ∈ B) → (x, f x) ∈ B := by
  classical
  obtain ⟨𝒰, hc, hφ, B', hB', rfl⟩ := exists_reduction B hB
  have : Countable ↥𝒰 := hc.to_subtype
  have hA : AnalyticSet B' := hB'.analyticSet
  obtain ⟨ψ, hψ, hψB⟩ := jankov_von_neumann_core B' hA
  let D : Set (↥𝒰 → Bool) := Prod.fst '' B'
  let F : (↥𝒰 → Bool) → ℝ := fun z => if h : z ∈ D then ψ ⟨z, h⟩ else 0
  have hν : IsProbabilityMeasure (μ.map (codeMap 𝒰)) := ⟨by rw [Measure.map_apply hφ MeasurableSet.univ]; simp⟩
  have hF : NullMeasurable F (μ.map (codeMap 𝒰)) := by
    intro s hs
    have : F ⁻¹' s = Subtype.val '' (ψ ⁻¹' s) ∪ (if (0:ℝ) ∈ s then Dᶜ else ∅) := by
      ext z
      by_cases h : z ∈ D
      · have hFz : F z = ψ ⟨z, h⟩ := by simp only [F, dif_pos h]
        simp only [mem_preimage, hFz, mem_union, mem_image]
        constructor
        · intro hz; exact Or.inl ⟨⟨z, h⟩, hz, rfl⟩
        · rintro (⟨⟨z', h'⟩, hz', rfl⟩ | h2)
          · exact hz'
          · split_ifs at h2 with h0
            · exact absurd h h2
            · exact absurd h2 (notMem_empty _)
      · have hFz : F z = 0 := by simp only [F, dif_neg h]
        simp only [mem_preimage, hFz, mem_union, mem_image]
        constructor
        · intro hz
          refine Or.inr ?_
          rw [if_pos hz]; exact h
        · rintro (⟨⟨z', h'⟩, hz', rfl⟩ | h2)
          · exact absurd h' h
          · split_ifs at h2 with h0
            · exact h0
            · exact absurd h2 (notMem_empty _)
    rw [this]
    have h1 : IsUniversallyMeasurable (Subtype.val '' (ψ ⁻¹' s)) :=
      cm_am_um _ (hψ.2 s hs)
    have h2 : IsUniversallyMeasurable D := cm_am_um _ hψ.1
    have h3 : IsUniversallyMeasurable (if (0:ℝ) ∈ s then Dᶜ else ∅) := by
      split_ifs
      · exact fun p hp => (h2 p hp).compl
      · exact fun p hp => nullMeasurableSet_empty
    exact (h1 _ hν).union (h3 _ hν)
  have hF' : AEMeasurable F (μ.map (codeMap 𝒰)) := hF.aemeasurable
  have hFφ : AEMeasurable (F ∘ codeMap 𝒰) μ :=
    hF'.comp_quasiMeasurePreserving (hφ.quasiMeasurePreserving μ)
  refine ⟨hFφ.mk _, hFφ.measurable_mk, ?_⟩
  filter_upwards [hFφ.ae_eq_mk] with x hx ⟨t, ht⟩
  have hxD : codeMap 𝒰 x ∈ D := ⟨_, ht, rfl⟩
  have h1 := hψB ⟨codeMap 𝒰 x, hxD⟩
  have h2 : F (codeMap 𝒰 x) = ψ ⟨codeMap 𝒰 x, hxD⟩ := by simp [F, dif_pos hxD]
  show (codeMap 𝒰 x, hFφ.mk _ x) ∈ B'
  rw [← hx]
  simp only [Function.comp, h2]
  exact h1

end Projection

section Main
variable {X : Type*} [MeasurableSpace X]

lemma measurable_innerRisk_prod (L : Loss X) (κ : X → Measure ℝ) (hκ : Measurable κ)
    (hκprob : ∀ x, IsProbabilityMeasure (κ x)) :
    Measurable (fun p : X × ℝ => innerRisk L (κ p.1) p.1 p.2) := by
  let k : ProbabilityTheory.Kernel X ℝ := ⟨κ, hκ⟩
  haveI : ProbabilityTheory.IsMarkovKernel k := ⟨hκprob⟩
  let η : ProbabilityTheory.Kernel (X × ℝ) ℝ := ProbabilityTheory.Kernel.comap k Prod.fst measurable_fst
  have hf : Measurable (fun q : (X × ℝ) × ℝ => ENNReal.ofReal (L q.1.1 q.2 q.1.2)) := by
    have h1 : Measurable (fun q : (X × ℝ) × ℝ => (q.1.1, q.2, q.1.2)) := by fun_prop
    exact ENNReal.measurable_ofReal.comp (L.measurable.comp h1)
  have := Measurable.lintegral_kernel_prod_right' (κ := η) hf
  convert this using 1
  funext a
  simp [innerRisk, η, ProbabilityTheory.Kernel.comap_apply, k]

lemma measurable_iInf_of_complete (hX : IsCompleteMeasurableSpace X) (h : X × ℝ → ℝ≥0∞)
    (hh : Measurable h) : Measurable (fun x => ⨅ t : ℝ, h (x, t)) := by
  refine measurable_of_Iio (fun c => ?_)
  have : {x | (⨅ t : ℝ, h (x, t)) < c} = Prod.fst '' {p : X × ℝ | h p < c} := by
    ext x
    simp only [mem_setOf_eq, iInf_lt_iff, mem_image, Prod.exists, exists_and_right, exists_eq_right]
  rw [show (fun x => ⨅ t : ℝ, h (x, t)) ⁻¹' Iio c = {x | (⨅ t : ℝ, h (x, t)) < c} from rfl, this]
  apply hX
  intro μ hμ
  exact proj_nullMeasurable μ _ (measurableSet_lt hh measurable_const)

end Main

section Main2
variable {X : Type*} [MeasurableSpace X]

lemma approx_selection (hX : IsCompleteMeasurableSpace X) (h : X × ℝ → ℝ≥0∞)
    (hh : Measurable h) (μ : Measure X) [IsProbabilityMeasure μ]
    (ε : ℝ≥0∞) (hε0 : 0 < ε) (hεtop : ε ≠ ⊤) :
    ∃ f : X → ℝ, Measurable f ∧
      ∀ᵐ x ∂μ, (⨅ t : ℝ, h (x, t)) < ⊤ → h (x, f x) < (⨅ t : ℝ, h (x, t)) + ε := by
  classical
  have hm : Measurable (fun x => ⨅ t : ℝ, h (x, t)) := measurable_iInf_of_complete hX h hh
  set m : X → ℝ≥0∞ := fun x => ⨅ t : ℝ, h (x, t) with hm_def
  have hδ0 : 0 < ε / 2 := ENNReal.half_pos hε0.ne'
  have hδε : ε / 2 < ε := ENNReal.half_lt_self hε0.ne' hεtop
  have hδtop : ε / 2 ≠ ⊤ := ne_top_of_lt hδε
  set δ := ε / 2 with hδ
  have hsel : ∀ k : ℕ, ∃ g : X → ℝ, Measurable g ∧
      ∀ᵐ x ∂μ, (∃ t, h (x, t) < ((k : ℝ≥0∞) + 1) * δ) → h (x, g x) < ((k : ℝ≥0∞) + 1) * δ := by
    intro k
    exact exists_measurable_section μ {p : X × ℝ | h p < ((k : ℝ≥0∞) + 1) * δ}
      (measurableSet_lt hh measurable_const)
  choose g hg hga using hsel
  have hae : ∀ᵐ x ∂μ, ∀ k : ℕ, (∃ t, h (x, t) < ((k : ℝ≥0∞) + 1) * δ) →
      h (x, g k x) < ((k : ℝ≥0∞) + 1) * δ := ae_all_iff.2 hga
  let P : ℕ → X → Prop := fun k x => m x < ((k : ℝ≥0∞) + 1) * δ ∨ m x = ⊤
  have hP : ∀ x, ∃ N, P N x := by
    intro x
    by_cases hx : m x = ⊤
    · exact ⟨0, Or.inr hx⟩
    · obtain ⟨n, hn⟩ := ENNReal.exists_nat_mul_gt hδ0.ne' hx
      refine ⟨n, Or.inl (lt_of_lt_of_le hn ?_)⟩
      exact mul_le_mul_left (by simp) _
  have hPm : ∀ k, MeasurableSet {x | P k x} := by
    intro k
    exact (measurableSet_lt hm measurable_const).union (hm (measurableSet_singleton ⊤))
  refine ⟨fun x => g (Nat.find (hP x)) x, Measurable.find hg hPm hP, ?_⟩
  filter_upwards [hae] with x hx hmx
  have hK := Nat.find_spec (hP x)
  set K := Nat.find (hP x) with hKdef
  have hK1 : m x < ((K : ℝ≥0∞) + 1) * δ := by
    rcases hK with h1 | h1
    · exact h1
    · exact absurd h1 hmx.ne
  have hex : ∃ t, h (x, t) < ((K : ℝ≥0∞) + 1) * δ := by
    have := hK1
    simp only [hm_def, iInf_lt_iff] at this
    exact this
  have h2 := hx K hex
  have h3 : ((K : ℝ≥0∞) + 1) * δ ≤ m x + δ := by
    rcases Nat.eq_zero_or_pos K with h0 | hpos
    · rw [h0]; simp
    · obtain ⟨K', hK'⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
      have hmin : ¬ P K' x := Nat.find_min (hP x) (by omega)
      have h4 : ((K' : ℝ≥0∞) + 1) * δ ≤ m x := by
        by_contra hc
        exact hmin (Or.inl (not_le.1 hc))
      calc ((K : ℝ≥0∞) + 1) * δ = ((K' : ℝ≥0∞) + 1) * δ + δ := by
            rw [hK']; push_cast; ring
        _ ≤ m x + δ := add_le_add h4 le_rfl
  have h5 : m x + δ < m x + ε := ENNReal.add_lt_add_left hmx.ne hδε
  exact h2.trans_le (h3.trans h5.le)

end Main2

section Main3
variable {X : Type*} [MeasurableSpace X]

theorem lemma34_core (hX : IsCompleteMeasurableSpace X) (L : Loss X)
    (PX : Measure X) [IsProbabilityMeasure PX] (κ : X → Measure ℝ) (hκ : Measurable κ)
    (hκprob : ∀ x, IsProbabilityMeasure (κ x)) :
    Measurable (fun x => minInnerRisk L (κ x) x) ∧
      bayesRisk L PX κ = ∫⁻ x, minInnerRisk L (κ x) x ∂PX := by
  have hh := measurable_innerRisk_prod L κ hκ hκprob
  have hm : Measurable (fun x => minInnerRisk L (κ x) x) :=
    measurable_iInf_of_complete hX _ hh
  refine ⟨hm, le_antisymm ?_ ?_⟩
  · by_cases htop : ∫⁻ x, minInnerRisk L (κ x) x ∂PX = ⊤
    · rw [htop]; exact le_top
    refine ENNReal.le_of_forall_pos_le_add (fun ε hε _ => ?_)
    obtain ⟨f, hf, hae⟩ := approx_selection hX (fun p => innerRisk L (κ p.1) p.1 p.2) hh PX ε
      (by exact_mod_cast hε) ENNReal.coe_ne_top
    have hlt : ∀ᵐ x ∂PX, minInnerRisk L (κ x) x < ⊤ := ae_lt_top hm htop
    calc bayesRisk L PX κ ≤ outerRisk L PX κ f := iInf₂_le f hf
      _ ≤ ∫⁻ x, (minInnerRisk L (κ x) x + ε) ∂PX := by
          refine lintegral_mono_ae ?_
          filter_upwards [hae, hlt] with x h1 h2
          exact (h1 h2).le
      _ = ∫⁻ x, minInnerRisk L (κ x) x ∂PX + ε := by
          rw [lintegral_add_right _ measurable_const]; simp
  · exact le_iInf₂ (fun f hf => lintegral_mono (fun x => iInf_le _ (f x)))

theorem lemma311_core (hX : IsCompleteMeasurableSpace X) (L : Loss X)
    (PX : Measure X) [IsProbabilityMeasure PX] (κ : X → Measure ℝ) (hκ : Measurable κ)
    (hκprob : ∀ x, IsProbabilityMeasure (κ x))
    (ε : ENNReal) (hε : 0 < ε) :
    (∀ᵐ x ∂PX, minInnerRisk L (κ x) x < ⊤) ↔
      ∃ f : X → ℝ, Measurable f ∧ ∀ᵐ x ∂PX, f x ∈ approxMinimizers L (κ x) x ε := by
  have hh := measurable_innerRisk_prod L κ hκ hκprob
  constructor
  · intro hlt
    have hε' : 0 < min ε 1 := lt_min hε zero_lt_one
    have hε'top : min ε 1 ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _)
    obtain ⟨f, hf, hae⟩ := approx_selection hX (fun p => innerRisk L (κ p.1) p.1 p.2) hh PX
      (min ε 1) hε' hε'top
    refine ⟨f, hf, ?_⟩
    filter_upwards [hae, hlt] with x h1 h2
    exact (h1 h2).trans_le (add_le_add le_rfl (min_le_left _ _))
  · rintro ⟨f, hf, hae⟩
    filter_upwards [hae] with x hx
    by_contra hcon
    have h1 : minInnerRisk L (κ x) x = ⊤ := not_lt_top_iff.1 hcon
    have h2 : innerRisk L (κ x) x (f x) < minInnerRisk L (κ x) x + ε := hx
    have h3 : minInnerRisk L (κ x) x ≤ innerRisk L (κ x) x (f x) := iInf_le _ (f x)
    rw [h1] at h2 h3
    simp only [top_add, top_le_iff] at h2 h3
    rw [h3] at h2
    exact lt_irrefl _ h2

end Main3

end SupportVectorMachines.Calibration

open SupportVectorMachines.Calibration


theorem solution {X : Type*} [MeasurableSpace X]
    (hX : IsCompleteMeasurableSpace X) (L : Loss X)
    (PX : Measure X) [IsProbabilityMeasure PX] (κ : X → Measure ℝ) (hκ : Measurable κ)
    (hκprob : ∀ x, IsProbabilityMeasure (κ x)) :
    Measurable (fun x => minInnerRisk L (κ x) x) ∧
      bayesRisk L PX κ = ∫⁻ x, minInnerRisk L (κ x) x ∂PX := by
  exact lemma34_core hX L PX κ hκ hκprob
