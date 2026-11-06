-- Prove2me | solution 1 for ProbMetricStab.MixedInt.theorem_3_6
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T00:49:56.829217+00:00
-- url     : https://prove2.me/submissions/5ff18d60-a137-4b2c-942a-ace98d192a54
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ProbMetricStab_MixedInt_Setting
import Theorems.Thm_ProbMetricStab_MixedInt_lemma_3_5_b
import Theorems.Thm_ProbMetricStab_MixedInt_growth_bound
import Theorems.Thm_ProbMetricStab_MixedInt_theorem_2_2_d0
import Theorems.Thm_ProbMetricStab_MixedInt_theorem_2_3_d0
import Theorems.Thm_ProbMetricStab_MixedInt_estimate_12

open MeasureTheory Matrix
open scoped ENNReal NNReal

namespace ProbMetricStab.MixedInt.Thm36Aux

open ProbMetricStab.MixedInt

/-- The integrand restricted to `X`: equal to `f` on `X` and `+∞` off `X`. -/
noncomputable def restr {m s : ℕ}
    (f : EuclideanSpace ℝ (Fin s) → EuclideanSpace ℝ (Fin m) → EReal)
    (X : Set (EuclideanSpace ℝ (Fin m))) :
    EuclideanSpace ℝ (Fin s) → EuclideanSpace ℝ (Fin m) → EReal :=
  open Classical in fun ξ x => if x ∈ X then f ξ x else ⊤

section congr

variable {m s : ℕ} {f g : EuclideanSpace ℝ (Fin s) → EuclideanSpace ℝ (Fin m) → EReal}
  {X : Set (EuclideanSpace ℝ (Fin m))} (h : ∀ ξ, ∀ x ∈ X, f ξ x = g ξ x)
include h

lemma intObj_congr (ν : Measure (EuclideanSpace ℝ (Fin s))) {x : EuclideanSpace ℝ (Fin m)}
    (hx : x ∈ X) : intObj f ν x = intObj g ν x := by
  unfold intObj
  congr 1
  funext ξ
  exact h ξ x hx

lemma optVal_congr (ν : Measure (EuclideanSpace ℝ (Fin s))) : optVal f X ν = optVal g X ν := by
  unfold optVal
  exact iInf_congr fun x => iInf_congr fun hx => intObj_congr h ν hx

lemma solSet_congr (ν : Measure (EuclideanSpace ℝ (Fin s))) : solSet f X ν = solSet g X ν := by
  ext x
  simp only [solSet, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hx, e⟩
    exact ⟨hx, by rw [← intObj_congr h ν hx, ← optVal_congr h ν, e]⟩
  · rintro ⟨hx, e⟩
    exact ⟨hx, by rw [intObj_congr h ν hx, optVal_congr h ν, e]⟩

lemma locOptVal_congr (U : Set (EuclideanSpace ℝ (Fin m))) (ν : Measure (EuclideanSpace ℝ (Fin s))) :
    locOptVal f X U ν = locOptVal g X U ν := by
  unfold locOptVal
  exact iInf_congr fun x => iInf_congr fun hx => intObj_congr h ν hx.1

lemma locSolSet_congr (U : Set (EuclideanSpace ℝ (Fin m)))
    (ν : Measure (EuclideanSpace ℝ (Fin s))) : locSolSet f X U ν = locSolSet g X U ν := by
  ext x
  simp only [locSolSet, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hx, e⟩
    exact ⟨hx, by rw [← intObj_congr h ν hx.1, ← locOptVal_congr h U ν, e]⟩
  · rintro ⟨hx, e⟩
    exact ⟨hx, by rw [intObj_congr h ν hx.1, locOptVal_congr h U ν, e]⟩

lemma isCLMSet_congr (U : Set (EuclideanSpace ℝ (Fin m)))
    (ν : Measure (EuclideanSpace ℝ (Fin s))) : IsCLMSet f X U ν ↔ IsCLMSet g X U ν := by
  unfold IsCLMSet
  rw [locSolSet_congr h U ν]

lemma dFU_congr (U : Set (EuclideanSpace ℝ (Fin m)))
    (μ ν : Measure (EuclideanSpace ℝ (Fin s))) : dFU f X U μ ν = dFU g X U μ ν := by
  unfold dFU
  exact iSup_congr fun x => iSup_congr fun hx => by
    rw [intObj_congr h μ hx.1, intObj_congr h ν hx.1]

lemma PFU_congr (Ξ : Set (EuclideanSpace ℝ (Fin s))) (U : Set (EuclideanSpace ℝ (Fin m))) :
    PFU Ξ f X U = PFU Ξ g X U := by
  ext ν
  simp only [PFU, Set.mem_ofPred_eq]
  have h1 : ∀ r : ℝ, (fun ξ => ⨅ x ∈ X ∩ Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) r, f ξ x)
      = (fun ξ => ⨅ x ∈ X ∩ Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) r, g ξ x) := by
    intro r
    funext ξ
    exact iInf_congr fun x => iInf_congr fun hx => h ξ x hx.1
  have h2 : (⨆ x ∈ X ∩ closure U, intObj f ν x) = ⨆ x ∈ X ∩ closure U, intObj g ν x :=
    iSup_congr fun x => iSup_congr fun hx => intObj_congr h ν hx.1
  simp_rw [h1, h2]

lemma growthInv_congr (U : Set (EuclideanSpace ℝ (Fin m)))
    (μ : Measure (EuclideanSpace ℝ (Fin s))) (t : ℝ≥0∞) :
    growthInv f X U μ t = growthInv g X U μ t := by
  have hψ : ∀ τ, growthFn f X U μ τ = growthFn g X U μ τ := by
    intro τ
    unfold growthFn
    rw [solSet_congr h μ, optVal_congr h μ]
    exact iInf_congr fun x => iInf_congr fun hx => by rw [intObj_congr h μ hx.1.1]
  unfold growthInv
  simp_rw [hψ]

lemma PsiThm23_congr (U : Set (EuclideanSpace ℝ (Fin m)))
    (μ : Measure (EuclideanSpace ℝ (Fin s))) (t : ℝ≥0∞) :
    PsiThm23 f X U μ t = PsiThm23 g X U μ t := by
  unfold PsiThm23
  rw [growthInv_congr h U μ]

end congr

section mono

variable {m s : ℕ} (f : EuclideanSpace ℝ (Fin s) → EuclideanSpace ℝ (Fin m) → EReal)
  (X U : Set (EuclideanSpace ℝ (Fin m))) (μ : Measure (EuclideanSpace ℝ (Fin s)))

lemma growthInv_mono {t t' : ℝ≥0∞} (htt : t ≤ t') :
    growthInv f X U μ t ≤ growthInv f X U μ t' := by
  unfold growthInv
  refine iSup₂_le fun τ hτ => ?_
  exact le_iSup₂_of_le (f := fun (τ : ℝ≥0) (_ : growthFn f X U μ τ ≤ (t' : EReal)) => (τ : ℝ≥0∞))
    τ (hτ.trans (EReal.coe_ennreal_le_coe_ennreal_iff.2 htt)) le_rfl

lemma PsiThm23_le_PsiCor28 {η η' : ℝ≥0∞} (hη : η ≤ η') :
    PsiThm23 f X U μ η ≤ PsiCor28 f X U μ η' := by
  unfold PsiThm23 PsiCor28
  gcongr
  exact growthInv_mono f X U μ (hη.trans (by
      calc η' = 1 * η' := (one_mul _).symm
        _ ≤ 2 * η' := by gcongr; norm_num))

end mono

lemma addBall_mono {m : ℕ} (A : Set (EuclideanSpace ℝ (Fin m))) {R R' : ℝ≥0∞} (h : R ≤ R') :
    addBall A R ⊆ addBall A R' := by
  rintro x ⟨a, ha, hxa⟩
  exact ⟨a, ha, hxa.trans h⟩

lemma isClosed_of_isPolyhedron {s : ℕ} {Ξ : Set (EuclideanSpace ℝ (Fin s))}
    (hΞ : IsPolyhedron Ξ) : IsClosed Ξ := by
  obtain ⟨k, a, b, rfl⟩ := hΞ
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun i => isClosed_le (continuous_const.inner continuous_id) continuous_const

lemma PpK_subset_Pp_one {s : ℕ} (Ξ : Set (EuclideanSpace ℝ (Fin s))) {p K : ℝ} (hp : 1 < p) :
    PpK Ξ p K ⊆ Pp Ξ 1 := by
  rintro ν ⟨⟨hprob, hfin⟩, -⟩
  refine ⟨hprob, ?_⟩
  have : IsProbabilityMeasure ν := hprob.1
  have hle : ∀ ξ : EuclideanSpace ℝ (Fin s), ENNReal.ofReal (‖ξ‖ ^ (1 : ℝ)) ≤
      (fun _ => (1 : ℝ≥0∞)) ξ + ENNReal.ofReal (‖ξ‖ ^ p) := by
    intro ξ
    rw [Real.rpow_one]
    calc ENNReal.ofReal ‖ξ‖ ≤ ENNReal.ofReal (1 + ‖ξ‖ ^ p) := by
          apply ENNReal.ofReal_le_ofReal
          rcases le_or_gt ‖ξ‖ 1 with h1 | h1
          · have : 0 ≤ ‖ξ‖ ^ p := Real.rpow_nonneg (norm_nonneg _) _
            linarith
          · have : ‖ξ‖ ≤ ‖ξ‖ ^ p := by
              calc ‖ξ‖ = ‖ξ‖ ^ (1 : ℝ) := (Real.rpow_one _).symm
                _ ≤ ‖ξ‖ ^ p := Real.rpow_le_rpow_of_exponent_le h1.le hp.le
            linarith
      _ ≤ ENNReal.ofReal 1 + ENNReal.ofReal (‖ξ‖ ^ p) := ENNReal.ofReal_add_le
      _ = 1 + ENNReal.ofReal (‖ξ‖ ^ p) := by rw [ENNReal.ofReal_one]
  calc ∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ (1 : ℝ)) ∂ν
      ≤ ∫⁻ ξ, ((fun _ => (1 : ℝ≥0∞)) ξ + ENNReal.ofReal (‖ξ‖ ^ p)) ∂ν := lintegral_mono hle
    _ = ∫⁻ _, (1 : ℝ≥0∞) ∂ν + ∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ p) ∂ν :=
        lintegral_add_left measurable_const _
    _ < ∞ := by
        rw [lintegral_const, measure_univ, one_mul]
        exact ENNReal.add_lt_top.2 ⟨ENNReal.one_lt_top, hfin⟩

/-- The projection of a closed subset of a product of proper metric spaces is Borel. -/
lemma measurableSet_fst_image_of_isClosed {A B : Type*} [MetricSpace A] [ProperSpace A]
    [MeasurableSpace A] [BorelSpace A] [MetricSpace B] [ProperSpace B]
    {C : Set (A × B)} (hC : IsClosed C) : MeasurableSet (Prod.fst '' C) := by
  have hσ : IsSigmaCompact C := IsSigmaCompact.of_isClosed_subset isSigmaCompact_univ hC
    (Set.subset_univ _)
  obtain ⟨K, hK, hKU⟩ := hσ.image continuous_fst
  rw [← hKU]
  exact MeasurableSet.iUnion fun n => (hK n).isClosed.measurableSet

/-- `f₀` restricted to `X` (and `+∞` off `X`) is a normal integrand on `Ξ`: it is jointly
lower semicontinuous on `Ξ × ℝ^m`. -/
lemma normal_integrand {m s r mh mb : ℕ} (P : MIProgram m s r mh mb) (hX : IsClosed P.X)
    (hΞ : IsClosed P.Ξ) (hlsc : LowerSemicontinuousOn P.recourse.Phi P.recourse.Tset)
    (hB2 : P.B2) : ProbMetricStab.TwoStage.IsNormalIntegrand P.Ξ (restr P.f0 P.X) := by
  classical
  set g : EuclideanSpace ℝ (Fin s) × EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin r) :=
    fun z => P.h z.1 - P.T z.1 z.2 with hg
  have hh : Continuous P.h := P.h.continuous_of_finiteDimensional
  have hT : Continuous P.T := P.T.continuous_of_finiteDimensional
  have hgc : Continuous g :=
    (hh.comp continuous_fst).sub ((hT.comp continuous_fst).clm_apply continuous_snd)
  set S : Set (EuclideanSpace ℝ (Fin s) × EuclideanSpace ℝ (Fin m)) := P.Ξ ×ˢ P.X with hS
  have hSc : IsClosed S := hΞ.prod hX
  set F : EuclideanSpace ℝ (Fin s) × EuclideanSpace ℝ (Fin m) → EReal :=
    fun z => if z ∈ S then P.f0 z.1 z.2 else ⊤ with hF
  have hmaps : Set.MapsTo g S P.recourse.Tset := fun z hz => hB2 _ hz.1 _ hz.2
  have hFl : LowerSemicontinuous F := by
    intro z y hy
    by_cases hz : z ∈ S
    · have h1 : LowerSemicontinuousWithinAt (fun w => P.recourse.Phi (g w)) S z := by
        intro y' hy'
        have := hlsc (g z) (hmaps hz) y' hy'
        exact (hgc.continuousWithinAt.tendsto_nhdsWithin hmaps).eventually this
      have h0 : LowerSemicontinuousWithinAt
          (fun w : EuclideanSpace ℝ (Fin s) × EuclideanSpace ℝ (Fin m) =>
            ((inner ℝ P.c w.2 : ℝ) : EReal)) S z :=
        (continuous_coe_real_ereal.comp
          (continuous_const.inner continuous_snd)).continuousWithinAt.lowerSemicontinuousWithinAt
      have h2 := h0.add' h1 (EReal.continuousAt_add (Or.inl (EReal.coe_ne_top _))
        (Or.inl (EReal.coe_ne_bot _)))
      have hFz : F z = ((inner ℝ P.c z.2 : ℝ) : EReal) + P.recourse.Phi (g z) := by
        simp [hF, hz, MIProgram.f0, hg]
      rw [hFz] at hy
      have := h2 y hy
      rw [eventually_nhdsWithin_iff] at this
      filter_upwards [this] with w hw
      by_cases hwS : w ∈ S
      · have hFw : F w = ((inner ℝ P.c w.2 : ℝ) : EReal) + P.recourse.Phi (g w) := by
          simp [hF, hwS, MIProgram.f0, hg]
        rw [hFw]; exact hw hwS
      · have hFw : F w = ⊤ := by simp [hF, hwS]
        rw [hFw]
        exact lt_of_lt_of_le hy le_top
    · have hFz : F z = ⊤ := by simp [hF, hz]
      rw [hFz] at hy
      filter_upwards [hSc.isOpen_compl.mem_nhds hz] with w hw
      have hFw : F w = ⊤ := by simp [hF, show w ∉ S from hw]
      rw [hFw]; exact hy
  have hEpi : IsClosed {q : (EuclideanSpace ℝ (Fin s) × EuclideanSpace ℝ (Fin m)) × EReal |
      F q.1 ≤ q.2} := hFl.isClosed_epigraph
  have hrestr : ∀ ξ ∈ P.Ξ, ∀ x, restr P.f0 P.X ξ x = F (ξ, x) := by
    intro ξ hξ x
    by_cases hx : x ∈ P.X
    · simp [restr, hF, hS, hξ, hx]
    · simp [restr, hF, hS, hx]
  refine ⟨fun ξ hξ => ?_, fun O hO => ?_⟩
  · have : ProbMetricStab.TwoStage.epi (restr P.f0 P.X ξ) =
        (fun p : EuclideanSpace ℝ (Fin m) × ℝ => ((ξ, p.1), (p.2 : EReal))) ⁻¹'
          {q | F q.1 ≤ q.2} := by
      ext p
      simp [ProbMetricStab.TwoStage.epi, hrestr ξ hξ]
    rw [this]
    exact hEpi.preimage ((continuous_const.prodMk continuous_fst).prodMk
      (continuous_coe_real_ereal.comp continuous_snd))
  · obtain ⟨Fn, hFn, -, hFnU, -⟩ := hO.exists_iUnion_isClosed
    set E : Set (EuclideanSpace ℝ (Fin s) × (EuclideanSpace ℝ (Fin m) × ℝ)) :=
      {q | F (q.1, q.2.1) ≤ (q.2.2 : EReal)} with hE
    have hEc : IsClosed E := hEpi.preimage
      ((continuous_fst.prodMk (continuous_fst.comp continuous_snd)).prodMk
        (continuous_coe_real_ereal.comp (continuous_snd.comp continuous_snd)))
    have hset : {ξ | ξ ∈ P.Ξ ∧ (ProbMetricStab.TwoStage.epi (restr P.f0 P.X ξ) ∩ O).Nonempty} =
        P.Ξ ∩ ⋃ n, Prod.fst '' (E ∩ (Set.univ ×ˢ Fn n)) := by
      ext ξ
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iUnion, Set.mem_image]
      constructor
      · rintro ⟨hξ, ⟨p, hpE, hpO⟩⟩
        rw [← hFnU] at hpO
        obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hpO
        refine ⟨hξ, n, (ξ, p), ⟨?_, Set.mem_univ _, hn⟩, rfl⟩
        simp only [hE, Set.mem_ofPred_eq]
        rw [← hrestr ξ hξ]
        exact hpE
      · rintro ⟨hξ, n, q, ⟨hqE, -, hqn⟩, rfl⟩
        refine ⟨hξ, q.2, ?_, ?_⟩
        · simp only [ProbMetricStab.TwoStage.epi, Set.mem_ofPred_eq]
          rw [hrestr q.1 hξ]
          exact hqE
        · rw [← hFnU]; exact Set.mem_iUnion.2 ⟨n, hqn⟩
    rw [hset]
    exact hΞ.measurableSet.inter (MeasurableSet.iUnion fun n =>
      measurableSet_fst_image_of_isClosed (hEc.inter (isClosed_univ.prod (hFn n))))

end ProbMetricStab.MixedInt.Thm36Aux

open ProbMetricStab.MixedInt ProbMetricStab.MixedInt.Thm36Aux in
theorem solution {m s r mh mb : ℕ} (P : ProbMetricStab.MixedInt.MIProgram m s r mh mb)
    (hX : IsClosed P.X) (hΞ : ProbMetricStab.MixedInt.IsPolyhedron P.Ξ)
    (hB1 : P.recourse.B1) (hB2 : P.B2) (hB3 : P.recourse.B3)
    {p K : ℝ} (hp : 1 < p) (hK : 0 < K)
    (μ : Measure (EuclideanSpace ℝ (Fin s))) (hμ : μ ∈ PpK P.Ξ p K)
    (hS : (solSet P.f0 P.X μ).Nonempty)
    (U : Set (EuclideanSpace ℝ (Fin m))) (hUo : IsOpen U) (hUb : Bornology.IsBounded U)
    (hSU : solSet P.f0 P.X μ ⊆ U) :
    ∃ L : ℝ, 0 < L ∧ ∃ δ : ℝ, 0 < δ ∧ ∃ k : ℕ, ∀ ν ∈ PpK P.Ξ p K,
      d1phk k μ ν < ENNReal.ofReal δ →
        optVal P.f0 P.X μ ≠ ⊤ ∧ optVal P.f0 P.X μ ≠ ⊥ ∧
        locOptVal P.f0 P.X U ν ≠ ⊤ ∧ locOptVal P.f0 P.X U ν ≠ ⊥ ∧
        |(optVal P.f0 P.X μ).toReal - (locOptVal P.f0 P.X U ν).toReal| ≤
          L * (d1phk k μ ν).toReal ^ (1 / (1 + (r : ℝ) / (p - 1))) ∧
        (locSolSet P.f0 P.X U ν).Nonempty ∧
        locSolSet P.f0 P.X U ν ⊆
          addBall (solSet P.f0 P.X μ)
            (PsiCor28 P.f0 P.X U μ
              (ENNReal.ofReal (L * (d1phk k μ ν).toReal ^ (1 / (1 + (r : ℝ) / (p - 1)))))) ∧
        IsCLMSet P.f0 P.X U ν := by
  classical
  set e : ℝ := 1 / (1 + (r : ℝ) / (p - 1)) with he
  have hp1 : 0 < p - 1 := by linarith
  have he_pos : 0 < e := by
    have : 0 ≤ (r : ℝ) / (p - 1) := div_nonneg (Nat.cast_nonneg _) hp1.le
    rw [he]; positivity
  have hΞc : IsClosed P.Ξ := isClosed_of_isPolyhedron hΞ
  have hXne : P.X.Nonempty := hS.mono fun x hx => hx.1
  obtain ⟨-, hlsc, -⟩ := lemma_3_5_b P.recourse hB1 hB3
  obtain ⟨α, β, -, -, -, -, hPFU⟩ := growth_bound P hB1 hB2 hB3
  have hPFU' : ∀ ν ∈ PpK P.Ξ p K, ν ∈ PFU P.Ξ P.f0 P.X U := fun ν hν =>
    hPFU U hUb (PpK_subset_Pp_one P.Ξ hp hν)
  have hcong : ∀ ξ, ∀ x ∈ P.X, restr P.f0 P.X ξ x = P.f0 ξ x := by
    intro ξ x hx; simp [restr, hx]
  have hNI := normal_integrand P hX hΞc hlsc hB2
  have hPFUeq := PFU_congr hcong P.Ξ U
  have hμF : μ ∈ PFU P.Ξ (restr P.f0 P.X) P.X U := by rw [hPFUeq]; exact hPFU' μ hμ
  have hS' : (solSet (restr P.f0 P.X) P.X μ).Nonempty := by rwa [solSet_congr hcong]
  have hSU' : solSet (restr P.f0 P.X) P.X μ ⊆ U := by rwa [solSet_congr hcong]
  obtain ⟨-, h22b, δ₁, hδ₁, h22c⟩ :=
    theorem_2_2_d0 P.Ξ hΞc P.X hX hXne _ hNI U hUo hUb μ hμF hS' hSU'
  obtain ⟨Lhat, hLhat, h23⟩ :=
    theorem_2_3_d0 P.Ξ hΞc P.X hX hXne _ hNI U hUo hUb μ hμF hS' hSU'
  obtain ⟨C, hC, k, η₀, hη₀, h12⟩ := estimate_12 P hX hΞ hB1 hB2 hB3 hp hK μ hμ U hUo hUb
  have hρpos : 0 < (δ₁ / (2 * C)) ^ (1 / e) := Real.rpow_pos_of_pos (by positivity) _
  refine ⟨Lhat * C, by positivity, min η₀ ((δ₁ / (2 * C)) ^ (1 / e)), lt_min hη₀ hρpos, k, ?_⟩
  intro ν hν hd
  have hνF : ν ∈ PFU P.Ξ (restr P.f0 P.X) P.X U := by rw [hPFUeq]; exact hPFU' ν hν
  have hd1 : d1phk k μ ν < ENNReal.ofReal η₀ :=
    lt_of_lt_of_le hd (ENNReal.ofReal_le_ofReal (min_le_left _ _))
  have hdF := h12 ν hν hd1
  have hdtop : d1phk k μ ν ≠ ⊤ := ne_top_of_lt hd
  set D := (d1phk k μ ν).toReal with hD
  have hD0 : 0 ≤ D := ENNReal.toReal_nonneg
  have hDlt : D < (δ₁ / (2 * C)) ^ (1 / e) := by
    have h1 : ENNReal.ofReal D < ENNReal.ofReal (min η₀ ((δ₁ / (2 * C)) ^ (1 / e))) := by
      rw [hD, ENNReal.ofReal_toReal hdtop]; exact hd
    have h2 := (ENNReal.ofReal_lt_ofReal_iff (lt_min hη₀ hρpos)).1 h1
    exact lt_of_lt_of_le h2 (min_le_right _ _)
  have hDe : D ^ e < δ₁ / (2 * C) := by
    calc D ^ e < ((δ₁ / (2 * C)) ^ (1 / e)) ^ e := Real.rpow_lt_rpow hD0 hDlt he_pos
      _ = δ₁ / (2 * C) := by
        rw [← Real.rpow_mul (by positivity), one_div_mul_cancel he_pos.ne', Real.rpow_one]
  have hDe0 : 0 ≤ D ^ e := Real.rpow_nonneg hD0 _
  have hCD : C * D ^ e < δ₁ := by
    have : C * D ^ e < C * (δ₁ / (2 * C)) := mul_lt_mul_of_pos_left hDe hC
    have h2 : C * (δ₁ / (2 * C)) = δ₁ / 2 := by field_simp
    linarith
  obtain ⟨hv1, hv2, hv3, hv4, hvle⟩ := h22b ν hνF
  rw [optVal_congr hcong, locOptVal_congr hcong, dFU_congr hcong] at hvle
  rw [optVal_congr hcong] at hv1 hv2
  rw [locOptVal_congr hcong] at hv3 hv4
  obtain ⟨hne, hsub⟩ := h23 ν hνF
  rw [locSolSet_congr hcong, solSet_congr hcong, PsiThm23_congr hcong, dFU_congr hcong] at hsub
  rw [locSolSet_congr hcong] at hne
  have hclm := h22c ν hνF
  rw [isCLMSet_congr hcong, dFU_congr hcong] at hclm
  have hCD0 : 0 ≤ C * D ^ e := mul_nonneg hC.le hDe0
  have hLD : C * D ^ e ≤ Lhat * C * D ^ e := by nlinarith
  refine ⟨hv1, hv2, hv3, hv4, ?_, hne, ?_, ?_⟩
  · have := (ENNReal.ofReal_le_ofReal_iff hCD0).1 (hvle.trans hdF)
    exact this.trans hLD
  · refine hsub.trans (addBall_mono _ ?_)
    apply PsiThm23_le_PsiCor28
    calc ENNReal.ofReal Lhat * dFU P.f0 P.X U μ ν
        ≤ ENNReal.ofReal Lhat * ENNReal.ofReal (C * D ^ e) := by gcongr
      _ = ENNReal.ofReal (Lhat * C * D ^ e) := by
        rw [← ENNReal.ofReal_mul (by linarith), mul_assoc]
  · apply hclm
    exact lt_of_le_of_lt hdF ((ENNReal.ofReal_lt_ofReal_iff hδ₁).2 hCD)
