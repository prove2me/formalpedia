-- Prove2me | solution 1 for TabooRegen.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-05T18:18:00.164838+00:00
-- url     : https://prove2.me/submissions/d2896bd3-0522-409a-8e6e-8986f8479a2d

import Mathlib
import Definitions.Def_TabooRegen_Window
import Theorems.Thm_TabooRegen_delay_shift
import Theorems.Thm_TabooRegen_uniform_convergence_4_2
import Theorems.Thm_TabooRegen_integral_btilde
import Theorems.Thm_TabooRegen_pstar_consistent
import Theorems.Thm_TabooRegen_proposition_2
import Theorems.Thm_TabooRegen_proposition_3

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

set_option autoImplicit false

namespace TabooRegen.Red

open TabooRegen TabooRegen.Model
open KurtzProtter91.Integrals (IsCadlag)

lemma isCadlag_comp' {E F : Type*} [TopologicalSpace E] [TopologicalSpace F] (x : ℝ≥0 → E)
    (hx : IsCadlag x) (f : E → F) (hf : Continuous f) : IsCadlag (f ∘ x) := by
  refine ⟨fun t => (hf.continuousAt).comp_continuousWithinAt (hx.1 t), fun t ht => ?_⟩
  obtain ⟨a, ha⟩ := hx.2 t ht
  exact ⟨f a, (hf.tendsto a).comp ha⟩

/-- coordinate projection of a window of `2K+1` cycles onto its middle `2k+1` cycles -/
def proj {β : Type*} (k K : ℕ) (w : Fin (2 * K + 1) → β) : Fin (2 * k + 1) → β :=
  fun i => w ⟨min (i.1 + (K - k)) (2 * K), by omega⟩

lemma proj_self {β : Type*} (k : ℕ) (w : Fin (2 * k + 1) → β) : proj k k w = w := by
  funext i
  simp only [proj]
  congr 1
  ext
  simp only
  have := i.2
  omega

lemma proj_succ {β : Type*} (k K : ℕ) (hk : k ≤ K) (w : Fin (2 * (K + 1) + 1) → β) :
    proj k (K + 1) w = proj k K (dropOuter K w) := by
  funext i
  simp only [proj, dropOuter]
  congr 1
  ext
  simp only
  have := i.2
  omega

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] {A : Set S}

lemma measurable_projP {k K : ℕ} :
    Measurable fun p : (Fin (2 * K + 1) → Path S) × ℝ => (proj k K p.1, p.2) :=
  (measurable_pi_lambda _ fun _ => (measurable_pi_apply _).comp measurable_fst).prodMk
    measurable_snd

section model
variable {Ω : Type*} [MeasurableSpace Ω] (M : Model S A Ω)

/-- the path of `X` in `S̃` -/
def pathOf (ω : Ω) : Path S :=
  ⟨fun t => Sum.inl (M.X ω t), isCadlag_comp' _ (M.cadlag ω) Sum.inl continuous_inl⟩

lemma measurable_pathOf : Measurable (pathOf M) := by
  refine Measurable.subtype_mk ?_
  exact measurable_pi_lambda _ fun t => measurable_inl.comp (M.measurable_X t)

lemma measurable_Γ : Measurable M.Γ :=
  M.exit_measurable.comp (measurable_pathOf M)

lemma T_monotone (ω : Ω) : Monotone fun n => M.T n ω :=
  monotone_nat_of_le_succ fun n => M.T_mono n ω

lemma lt_strad_iff (K : ℕ) (u : ℝ) (ω : Ω) :
    K < M.strad u ω ↔ M.T K ω ≤ ENNReal.ofReal u ∧ ∃ n, ENNReal.ofReal u < M.T n ω := by
  unfold Model.strad
  constructor
  · intro h
    have hne : {n : ℕ | ENNReal.ofReal u < M.T n ω}.Nonempty := by
      by_contra hne
      rw [Set.not_nonempty_iff_eq_empty] at hne
      rw [hne, Nat.sInf_empty] at h
      exact Nat.not_lt_zero _ h
    refine ⟨?_, hne⟩
    by_contra hK
    push_neg at hK
    exact absurd (Nat.sInf_le hK) (not_le.mpr h)
  · rintro ⟨hK, hne⟩
    have hmem : ENNReal.ofReal u < M.T (sInf {n : ℕ | ENNReal.ofReal u < M.T n ω}) ω :=
      Nat.sInf_mem hne
    by_contra h
    push_neg at h
    have := T_monotone M ω h
    exact absurd hK (not_le.mpr (lt_of_lt_of_le hmem this))

lemma measurableSet_lt_strad (K : ℕ) (u : ℝ) : MeasurableSet {ω | K < M.strad u ω} := by
  have : {ω | K < M.strad u ω} =
      {ω | M.T K ω ≤ ENNReal.ofReal u} ∩ ⋃ n, {ω | ENNReal.ofReal u < M.T n ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iUnion]
    exact lt_strad_iff M K u ω
  rw [this]
  exact (measurableSet_le (M.measurable_T K) measurable_const).inter
    (MeasurableSet.iUnion fun n => measurableSet_lt measurable_const (M.measurable_T n))

/-- the numerator event of Theorem 2 / (4.2) -/
def ev (k : ℕ) (B : Set ((Fin (2 * k + 1) → Path S) × ℝ)) (u : ℝ) : Set Ω :=
  {ω | k < M.strad u ω ∧ (M.win k u ω, M.age u ω) ∈ B ∧ ENNReal.ofReal u < M.Γ ω}

lemma measurableSet_ev_univ (K : ℕ) (u : ℝ) : MeasurableSet (ev M K Set.univ u) := by
  have : ev M K Set.univ u = {ω | K < M.strad u ω} ∩ {ω | ENNReal.ofReal u < M.Γ ω} := by
    ext ω
    simp [ev]
  rw [this]
  exact (measurableSet_lt_strad M K u).inter (measurableSet_lt measurable_const (measurable_Γ M))

lemma measurable_btilde (α : ℝ) (ℓ : ℕ) (B : Set ((Fin (2 * ℓ + 1) → Path S) × ℝ))
    (hB : MeasurableSet B) : Measurable (M.btilde α ℓ B) := by
  have h1 : Measurable fun p : ℝ × Ω =>
      ((fun i : Fin (2 * ℓ + 1) => M.W (1 + i) p.2), p.1 - (M.T ℓ p.2).toReal) :=
    (measurable_pi_lambda _ fun i => (M.measurable_W _).comp measurable_snd).prodMk
      (measurable_fst.sub ((M.measurable_T ℓ).ennreal_toReal.comp measurable_snd))
  have hE : MeasurableSet {p : ℝ × Ω |
      ((fun i : Fin (2 * ℓ + 1) => M.W (1 + i) p.2), p.1 - (M.T ℓ p.2).toReal) ∈ B ∧
      M.T ℓ p.2 ≤ ENNReal.ofReal p.1 ∧ ENNReal.ofReal p.1 < M.T (ℓ + 1) p.2 ∧
      ENNReal.ofReal p.1 < M.Γ p.2} :=
    (hB.preimage h1).inter ((measurableSet_le ((M.measurable_T ℓ).comp measurable_snd)
      (ENNReal.measurable_ofReal.comp measurable_fst)).inter
      ((measurableSet_lt (ENNReal.measurable_ofReal.comp measurable_fst)
        ((M.measurable_T (ℓ + 1)).comp measurable_snd)).inter
      (measurableSet_lt (ENNReal.measurable_ofReal.comp measurable_fst)
        ((measurable_Γ M).comp measurable_snd))))
  haveI : IsProbabilityMeasure M.P := M.isProb
  have h2 := (measurable_measure_prodMk_left (ν := M.P) hE).ennreal_toReal
  exact (Real.measurable_exp.comp (measurable_const.mul measurable_id)).mul h2

lemma win_proj {k K : ℕ} (hkK : k ≤ K) (u : ℝ) (ω : Ω) (hK : K < M.strad u ω) :
    M.win k u ω = proj k K (M.win K u ω) := by
  funext i
  have h : M.strad u ω - k + (i : ℕ) = M.strad u ω - K + min ((i : ℕ) + (K - k)) (2 * K) := by
    have := i.2
    omega
  simp only [Model.win, proj]
  rw [h]

lemma core_bound {kt K : ℕ} (hkK : kt ≤ K)
    (B : Set ((Fin (2 * kt + 1) → Path S) × ℝ)) (u x c1 L η : ℝ) (hx : 0 ≤ x)
    (hA : |x * (M.P (ev M K ((fun p => (proj kt K p.1, p.2)) ⁻¹' B) u)).toReal - c1 * L| ≤ η)
    (hU : |x * (M.P (ev M K Set.univ u)).toReal - c1| ≤ η)
    (hD : |x * (M.P {ω | ENNReal.ofReal u < M.Γ ω}).toReal - c1| ≤ η) :
    |x * (M.P (ev M kt B u)).toReal - c1 * L| ≤ 3 * η := by
  haveI : IsProbabilityMeasure M.P := M.isProb
  have hsub1 : ev M K ((fun p => (proj kt K p.1, p.2)) ⁻¹' B) u ⊆ ev M kt B u := by
    rintro ω ⟨hK, hB, hΓ⟩
    refine ⟨lt_of_le_of_lt hkK hK, ?_, hΓ⟩
    rw [win_proj M hkK u ω hK]
    exact hB
  have hsub2 : ev M kt B u ⊆ ev M K ((fun p => (proj kt K p.1, p.2)) ⁻¹' B) u ∪
      ({ω | ENNReal.ofReal u < M.Γ ω} \ ev M K Set.univ u) := by
    rintro ω ⟨hk, hB, hΓ⟩
    by_cases hK : K < M.strad u ω
    · left
      refine ⟨hK, ?_, hΓ⟩
      show (proj kt K (M.win K u ω), M.age u ω) ∈ B
      rw [← win_proj M hkK u ω hK]
      exact hB
    · right
      exact ⟨hΓ, fun h => hK h.1⟩
  have hsub3 : ev M K Set.univ u ⊆ {ω | ENNReal.ofReal u < M.Γ ω} := fun ω h => h.2.2
  have hdiff : M.P ({ω | ENNReal.ofReal u < M.Γ ω} \ ev M K Set.univ u) =
      M.P {ω | ENNReal.ofReal u < M.Γ ω} - M.P (ev M K Set.univ u) :=
    measure_diff hsub3 (measurableSet_ev_univ M K u).nullMeasurableSet (measure_ne_top _ _)
  have l1 := ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub1 (μ := M.P))
  have l2 : (M.P (ev M kt B u)).toReal ≤
      (M.P (ev M K ((fun p => (proj kt K p.1, p.2)) ⁻¹' B) u)).toReal +
        ((M.P {ω | ENNReal.ofReal u < M.Γ ω}).toReal - (M.P (ev M K Set.univ u)).toReal) := by
    have h := (measure_mono hsub2 (μ := M.P)).trans (measure_union_le _ _)
    rw [hdiff] at h
    have h' := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _,
      ENNReal.sub_ne_top (measure_ne_top _ _)⟩) h
    rwa [ENNReal.toReal_add (measure_ne_top _ _) (ENNReal.sub_ne_top (measure_ne_top _ _)),
      ENNReal.toReal_sub_of_le (measure_mono hsub3) (measure_ne_top _ _)] at h'
  have m1 := mul_le_mul_of_nonneg_left l1 hx
  have m2 := mul_le_mul_of_nonneg_left l2 hx
  rw [mul_add, mul_sub] at m2
  rw [abs_le] at hA hU hD ⊢
  constructor <;> linarith [hA.1, hA.2, hU.1, hU.2, hD.1, hD.2]

lemma PW_proj (α : ℝ)
    (hcons : ∀ (k : ℕ) (B : Set ((Fin (2 * k + 1) → Path S) × ℝ)), MeasurableSet B →
      M.PstarWindow α (k + 1) ((fun p => (dropOuter k p.1, p.2)) ⁻¹' B) = M.PstarWindow α k B)
    (k : ℕ) (B : Set ((Fin (2 * k + 1) → Path S) × ℝ)) (hB : MeasurableSet B) :
    ∀ m : ℕ, M.PstarWindow α (k + m) ((fun p => (proj k (k + m) p.1, p.2)) ⁻¹' B) =
      M.PstarWindow α k B
  | 0 => by
      show M.PstarWindow α k ((fun p => (proj k k p.1, p.2)) ⁻¹' B) = M.PstarWindow α k B
      simp only [proj_self]
      rfl
  | m + 1 => by
      have h1 : ((fun p : (Fin (2 * (k + (m + 1)) + 1) → Path S) × ℝ =>
            (proj k (k + (m + 1)) p.1, p.2)) ⁻¹' B) =
          (fun p : (Fin (2 * (k + m + 1) + 1) → Path S) × ℝ => (dropOuter (k + m) p.1, p.2)) ⁻¹'
            ((fun p : (Fin (2 * (k + m) + 1) → Path S) × ℝ => (proj k (k + m) p.1, p.2)) ⁻¹' B) := by
        ext p
        simp only [Set.mem_preimage]
        exact Iff.of_eq (congrArg (fun w => (w, p.2) ∈ B) (proj_succ k (k + m) (by omega) p.1))
      rw [h1]
      exact (hcons (k + m) _ (hB.preimage measurable_projP)).trans (PW_proj α hcons k B hB m)

end model


lemma PW_proj' {Ω : Type*} [MeasurableSpace Ω] (M : Model S A Ω) (α : ℝ)
    (hcons : ∀ (k : ℕ) (B : Set ((Fin (2 * k + 1) → Path S) × ℝ)), MeasurableSet B →
      M.PstarWindow α (k + 1) ((fun p => (dropOuter k p.1, p.2)) ⁻¹' B) = M.PstarWindow α k B)
    (k : ℕ) (B : Set ((Fin (2 * k + 1) → Path S) × ℝ)) (hB : MeasurableSet B) (K : ℕ)
    (hK : k ≤ K) :
    M.PstarWindow α K ((fun p => (proj k K p.1, p.2)) ⁻¹' B) = M.PstarWindow α k B := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hK
  exact PW_proj M α hcons k B hB m

/-- the integration step against the delay law, abstractly -/
lemma abstract_numer {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (S0 : Set Ω)
    (T0 : Ω → ℝ≥0∞) (hT0 : Measurable T0) (α t R Lc η η' Cb : ℝ) (F : ℝ → ℝ)
    (G : Ω → ℝ≥0∞) (hR : 0 ≤ R) (hRt : R ≤ t) (hη : 0 ≤ η) (hLc : 0 ≤ Lc)
    (hCb : 0 ≤ Cb)
    (hG : ∀ ω, G ω = if T0 ω ≤ ENNReal.ofReal t then
      ENNReal.ofReal (Real.exp (α * (T0 ω).toReal)) * ENNReal.ofReal (F (t - (T0 ω).toReal))
      else 0)
    (hFin : ∀ r, 0 ≤ r → r ≤ R → |F (t - r) - Lc| ≤ η')
    (hFb : ∀ u, 0 ≤ u → F u ≤ Cb)
    (hDtop : ∫⁻ ω in S0, ENNReal.ofReal (Real.exp (α * (T0 ω).toReal)) ∂μ ≠ ⊤)
    (htail : ∫⁻ ω in S0, {ω | ENNReal.ofReal R < T0 ω}.indicator
      (fun ω => ENNReal.ofReal (Real.exp (α * (T0 ω).toReal))) ω ∂μ ≤ ENNReal.ofReal η) :
    |(∫⁻ ω in S0, G ω ∂μ).toReal -
        Lc * (∫⁻ ω in S0, ENNReal.ofReal (Real.exp (α * (T0 ω).toReal)) ∂μ).toReal| ≤
      η' * (∫⁻ ω in S0, ENNReal.ofReal (Real.exp (α * (T0 ω).toReal)) ∂μ).toReal +
        (Lc + Cb) * η := by
  set w : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (Real.exp (α * (T0 ω).toReal)) with hw_def
  have hw : Measurable w :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul hT0.ennreal_toReal))
  set Dtot := ∫⁻ ω in S0, w ω ∂μ with hDtot
  set s1 : Set Ω := {ω | T0 ω ≤ ENNReal.ofReal R}
  set s2 : Set Ω := {ω | ENNReal.ofReal R < T0 ω}
  have hs1 : MeasurableSet s1 := measurableSet_le hT0 measurable_const
  have hs2 : MeasurableSet s2 := measurableSet_lt measurable_const hT0
  set DR := ∫⁻ ω in S0, s1.indicator w ω ∂μ
  set Tail := ∫⁻ ω in S0, s2.indicator w ω ∂μ
  have hη' : 0 ≤ η' := le_trans (abs_nonneg _) (hFin 0 le_rfl hR)
  -- facts about ω with T0 ω ≤ ofReal t
  have key : ∀ ω, T0 ω ≤ ENNReal.ofReal t →
      0 ≤ (T0 ω).toReal ∧ (T0 ω).toReal ≤ t ∧ T0 ω = ENNReal.ofReal (T0 ω).toReal := by
    intro ω h
    have hne : T0 ω ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top h
    refine ⟨ENNReal.toReal_nonneg, ?_, (ENNReal.ofReal_toReal hne).symm⟩
    have hR0 : 0 ≤ t := le_trans hR hRt
    exact ENNReal.toReal_le_of_le_ofReal hR0 h
  set c := Lc + η' with hc
  have hup : ∀ ω, G ω ≤ w ω * ENNReal.ofReal c + s2.indicator w ω * ENNReal.ofReal Cb := by
    intro ω
    rw [hG ω]
    split_ifs with hT
    · obtain ⟨h0, hrt, hT'⟩ := key ω hT
      by_cases hR' : T0 ω ≤ ENNReal.ofReal R
      · have hrR : (T0 ω).toReal ≤ R := ENNReal.toReal_le_of_le_ofReal hR hR'
        have := hFin _ h0 hrR
        rw [abs_le] at this
        have hle : ENNReal.ofReal (F (t - (T0 ω).toReal)) ≤ ENNReal.ofReal c :=
          ENNReal.ofReal_le_ofReal (by linarith [this.2])
        exact le_trans (by gcongr) le_self_add
      · have hin : ω ∈ s2 := by simp only [s2, Set.mem_ofPred_eq]; exact not_le.mp hR'
        rw [Set.indicator_of_mem hin]
        have hle : ENNReal.ofReal (F (t - (T0 ω).toReal)) ≤ ENNReal.ofReal Cb :=
          ENNReal.ofReal_le_ofReal (hFb _ (by linarith))
        exact le_trans (by gcongr) le_add_self
    · positivity
  have hlow : ∀ ω, s1.indicator w ω * ENNReal.ofReal (Lc - η') ≤ G ω := by
    intro ω
    by_cases h1 : ω ∈ s1
    · rw [Set.indicator_of_mem h1, hG ω]
      have hT : T0 ω ≤ ENNReal.ofReal t := le_trans h1 (ENNReal.ofReal_le_ofReal hRt)
      rw [if_pos hT]
      obtain ⟨h0, _, _⟩ := key ω hT
      have hrR : (T0 ω).toReal ≤ R := ENNReal.toReal_le_of_le_ofReal hR h1
      have := hFin _ h0 hrR
      rw [abs_le] at this
      exact mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal (by linarith [this.1])) (by positivity)
    · rw [Set.indicator_of_notMem h1, zero_mul]
      positivity
  -- integrate
  have hU : ∫⁻ ω in S0, G ω ∂μ ≤ Dtot * ENNReal.ofReal c + Tail * ENNReal.ofReal Cb := by
    calc ∫⁻ ω in S0, G ω ∂μ
        ≤ ∫⁻ ω in S0, (w ω * ENNReal.ofReal c + s2.indicator w ω * ENNReal.ofReal Cb) ∂μ :=
          lintegral_mono hup
      _ = Dtot * ENNReal.ofReal c + Tail * ENNReal.ofReal Cb := by
          rw [lintegral_add_left (hw.mul_const _), lintegral_mul_const _ hw,
            lintegral_mul_const _ (hw.indicator hs2)]
  have hL : DR * ENNReal.ofReal (Lc - η') ≤ ∫⁻ ω in S0, G ω ∂μ := by
    rw [← lintegral_mul_const _ (hw.indicator hs1)]
    exact lintegral_mono hlow
  have hsplit : Dtot ≤ DR + Tail := by
    rw [← lintegral_add_left (hw.indicator hs1)]
    refine lintegral_mono fun ω => ?_
    by_cases h1 : ω ∈ s1
    · rw [Set.indicator_of_mem h1]
      exact le_self_add
    · have h2 : ω ∈ s2 := by simp only [s2, Set.mem_ofPred_eq]; exact not_le.mp h1
      rw [Set.indicator_of_mem h2]
      exact le_add_self
  have hDRle : DR ≤ Dtot := lintegral_mono fun ω => Set.indicator_le_self _ _ ω
  have hDRtop : DR ≠ ⊤ := ne_top_of_le_ne_top hDtop hDRle
  have hTailtop : Tail ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top htail
  have hGtop : ∫⁻ ω in S0, G ω ∂μ ≠ ⊤ :=
    ne_top_of_le_ne_top (by finiteness) hU
  -- reals
  set Dt := Dtot.toReal
  set DRr := DR.toReal
  set a := (∫⁻ ω in S0, G ω ∂μ).toReal
  have hTailr : Tail.toReal ≤ η := ENNReal.toReal_le_of_le_ofReal hη htail
  have hc0 : 0 ≤ c := by rw [hc]; linarith
  have e : (Dtot * ENNReal.ofReal c + Tail * ENNReal.ofReal Cb).toReal =
      Dt * c + Tail.toReal * Cb := by
    rw [ENNReal.toReal_add (ENNReal.mul_ne_top hDtop ENNReal.ofReal_ne_top)
      (ENNReal.mul_ne_top hTailtop ENNReal.ofReal_ne_top), ENNReal.toReal_mul,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal hc0, ENNReal.toReal_ofReal hCb]
  have hU' : a ≤ Dt * c + Tail.toReal * Cb :=
    (ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top hDtop ENNReal.ofReal_ne_top,
      ENNReal.mul_ne_top hTailtop ENNReal.ofReal_ne_top⟩) hU).trans_eq e
  have hsplit' : Dt ≤ DRr + Tail.toReal := by
    have := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hDRtop, hTailtop⟩) hsplit
    rwa [ENNReal.toReal_add hDRtop hTailtop] at this
  have hDRr : DRr ≤ Dt := ENNReal.toReal_mono hDtop hDRle
  set m := max (Lc - η') 0 with hm
  have ha : DRr * m ≤ a := by
    have := ENNReal.toReal_mono hGtop hL
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal'] at this
  have hm0 : 0 ≤ m := le_max_right _ _
  have hm1 : Lc - η' ≤ m := le_max_left _ _
  have hm2 : m ≤ Lc := max_le (by linarith) hLc
  have hDt0 : 0 ≤ Dt := ENNReal.toReal_nonneg
  have hDRr0 : 0 ≤ DRr := ENNReal.toReal_nonneg
  have hT0r : 0 ≤ Tail.toReal := ENNReal.toReal_nonneg
  have e1 := mul_le_mul_of_nonneg_right (show Dt - η ≤ DRr by linarith) hm0
  have e2 := mul_le_mul_of_nonneg_left hm1 hDt0
  have e3 := mul_le_mul_of_nonneg_left hm2 hη
  have e4 := mul_le_mul_of_nonneg_right hTailr hCb
  have e5 := mul_nonneg hLc hη
  have e6 := mul_nonneg hCb hη
  rw [abs_le]
  constructor
  · nlinarith [sub_mul Dt η m, mul_sub Dt Lc η']
  · rw [hc] at hU'
    nlinarith [mul_add Dt Lc η']

end TabooRegen.Red

set_option maxHeartbeats 1000000 in
open TabooRegen TabooRegen.Model in
theorem solution {S : Type*} [TopologicalSpace S] [PolishSpace S] [MeasurableSpace S]
    [BorelSpace S]
    {A : Set S} {Ω : Type*} [MeasurableSpace Ω] (M : Model S A Ω)
    (hreg : M.IsWideSenseTabooRegen) {α : ℝ} (h1 : M.A1 α) (h2 : M.A2) (h3 : M.A3 α)
    (h4 : M.A4 α) (h5 : M.A5 α) (h6 : M.A6 α) (h7 : M.A7)
    (k : ℝ → ℕ) (hk : MonotoneOn k (Set.Ici 0))
    (hkg : ∃ c < M.rate α, ∀ᶠ t in atTop, (k t : ℝ) ≤ c * t) :
    ∀ ε > 0, ∀ᶠ t in atTop, ∀ B : Set ((Fin (2 * k t + 1) → Path S) × ℝ), MeasurableSet B →
      |(ProbabilityTheory.cond M.P {ω | ENNReal.ofReal t < M.Γ ω}
          {ω | k t < M.strad t ω ∧ (M.win (k t) t ω, M.age t ω) ∈ B}).toReal -
        (M.PstarWindow α (k t) B).toReal| ≤ ε := by
  intro ε hε
  haveI : IsProbabilityMeasure M.P := M.isProb
  -- the denominator (Proposition 3)
  obtain ⟨hc2, hd⟩ := proposition_3 M hreg h1 h2 h3 h4 h5 h6
  have hS0m : MeasurableSet {ω | M.T 0 ω ≤ M.Γ ω} :=
    measurableSet_le (M.measurable_T 0) (Red.measurable_Γ M)
  have hwm : Measurable fun ω => ENNReal.ofReal (Real.exp (α * (M.T 0 ω).toReal)) :=
    ENNReal.measurable_ofReal.comp
      (Real.measurable_exp.comp (measurable_const.mul (M.measurable_T 0).ennreal_toReal))
  have hc2eq : M.c2 α = (∫⁻ ω in {ω | M.T 0 ω ≤ M.Γ ω},
      ENNReal.ofReal (Real.exp (α * (M.T 0 ω).toReal)) ∂M.P).toReal * M.c1 α := rfl
  set Dtot := ∫⁻ ω in {ω | M.T 0 ω ≤ M.Γ ω}, ENNReal.ofReal (Real.exp (α * (M.T 0 ω).toReal)) ∂M.P
    with hDtot
  have hDt0 : 0 ≤ Dtot.toReal := ENNReal.toReal_nonneg
  have hDtpos : 0 < Dtot.toReal := by
    rcases hDt0.lt_or_eq with h | h
    · exact h
    · rw [hc2eq, ← h, zero_mul] at hc2
      exact absurd hc2 (lt_irrefl 0)
  have hc1pos : 0 < M.c1 α := by
    by_contra hneg
    push_neg at hneg
    have := mul_nonpos_of_nonneg_of_nonpos hDt0 hneg
    rw [hc2eq] at hc2
    linarith
  have hDtop : Dtot ≠ ⊤ := (ENNReal.toReal_pos_iff.mp hDtpos).2.ne
  have hP : M.P {ω | M.T 0 ω ≤ M.Γ ω} ≠ 0 := by
    intro h0
    have : Dtot = 0 := by
      rw [hDtot, Measure.restrict_eq_zero.mpr h0, lintegral_zero_measure]
    rw [this, ENNReal.toReal_zero] at hDtpos
    exact lt_irrefl 0 hDtpos
  -- the non-delayed version (delay_shift)
  obtain ⟨M', hreg', h0', hA1, hA2, hA3, hA4, hA7, hrate, hcw, hPN', hshift⟩ :=
    delay_shift M hreg hP
  have h1' := (hA1 α).2 h1
  have h2' := hA2.2 h2
  have h3' := (hA3 α).2 h3
  have h4' := (hA4 α).2 h4
  have h7' := hA7.2 h7
  haveI : IsProbabilityMeasure M'.P := M'.isProb
  have hlam : (M'.lamInv α).toReal = (M.lamInv α).toReal := by
    have := hrate α
    unfold Model.rate at this
    exact inv_inj.mp this
  have hc1eq : M'.c1 α = M.c1 α := by
    unfold Model.c1
    rw [hcw α, hlam]
  have hc1rate : M.c1 α = (M.cycleWeight α).toReal * M.rate α := by
    unfold Model.c1 Model.rate
    rw [div_eq_mul_inv]
  -- P* facts
  have hcons : ∀ (k : ℕ) (B : Set ((Fin (2 * k + 1) → Path S) × ℝ)), MeasurableSet B →
      M.PstarWindow α (k + 1) ((fun p => (dropOuter k p.1, p.2)) ⁻¹' B) =
        M.PstarWindow α k B :=
    fun k => (pstar_consistent M hreg h1 h4 k).2
  have hPWle : ∀ (k : ℕ) (B : Set ((Fin (2 * k + 1) → Path S) × ℝ)), MeasurableSet B →
      M.PstarWindow α k B ≤ 1 := by
    intro k B hB
    obtain ⟨μ, hμ, hμB⟩ := (pstar_consistent M hreg h1 h4 k).1
    rw [← hμB B hB]
    exact prob_le_one
  have hPWuniv : ∀ k : ℕ, M.PstarWindow α k Set.univ = 1 := by
    intro k
    obtain ⟨μ, hμ, hμB⟩ := (pstar_consistent M hreg h1 h4 k).1
    rw [← hμB _ MeasurableSet.univ]
    exact measure_univ
  have hcwpos : 0 < (M.cycleWeight α).toReal := by
    by_contra hneg
    push_neg at hneg
    have h0 : (M.cycleWeight α).toReal = 0 := le_antisymm hneg ENNReal.toReal_nonneg
    rw [hc1rate, h0, zero_mul] at hc1pos
    exact lt_irrefl 0 hc1pos
  have hcw0 : M.cycleWeight α ≠ 0 := (ENNReal.toReal_pos_iff.mp hcwpos).1.ne'
  have hcwtop : M.cycleWeight α ≠ ⊤ := (ENNReal.toReal_pos_iff.mp hcwpos).2.ne
  have hPN : ∀ (k : ℕ) (B : Set ((Fin (2 * k + 1) → Path S) × ℝ)),
      M.PstarNum α k B = M.PstarWindow α k B * M.cycleWeight α := fun k B => by
    unfold Model.PstarWindow
    rw [ENNReal.div_mul_cancel hcw0 hcwtop]
  -- identification of the limit (integral_btilde)
  have hident : ∀ (K : ℕ) (B' : Set ((Fin (2 * K + 1) → Path S) × ℝ)), MeasurableSet B' →
      M'.rate α * ∫ u in Set.Ioi 0, M'.btilde α K B' u =
        M.c1 α * (M.PstarWindow α K B').toReal := by
    intro K B' hB'
    have hint : ∫ u in Set.Ioi 0, M'.btilde α K B' u = (M'.PstarNum α K B').toReal := by
      rw [integral_eq_lintegral_of_nonneg_ae,
        integral_btilde M' hreg' h0' h1' h2' h3' h4' h7' K B' hB']
      · exact ae_of_all _ fun u => mul_nonneg (Real.exp_pos _).le ENNReal.toReal_nonneg
      · exact (Red.measurable_btilde M' α K B' hB').aestronglyMeasurable
    rw [hint, hPN' α K B', hPN K B', ENNReal.toReal_mul, hrate α, hc1rate]
    ring
  -- Proposition 2 for the non-delayed version, and a uniform bound
  obtain ⟨-, hd'⟩ := proposition_2 M' hreg' h0' h1' h2' h3' h4'
  rw [hc1eq] at hd'
  set c1 := M.c1 α with hc1def
  obtain ⟨u1, hu1⟩ := eventually_atTop.mp (hd'.eventually (eventually_le_nhds (lt_add_one c1)))
  set Cb := max (c1 + 1) (Real.exp (α * u1)) with hCb
  have hCb0 : 0 ≤ Cb := le_trans (by linarith) (le_max_left _ _)
  have hFb : ∀ (kt : ℕ) (B : Set ((Fin (2 * kt + 1) → Path S) × ℝ)) (u : ℝ), 0 ≤ u →
      Real.exp (α * u) * (M'.P (Red.ev M' kt B u)).toReal ≤ Cb := by
    intro kt B u hu
    have hsub : (M'.P (Red.ev M' kt B u)).toReal ≤
        (M'.P {ω | ENNReal.ofReal u < M'.Γ ω}).toReal :=
      ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono fun ω h => h.2.2)
    have he := (Real.exp_pos (α * u)).le
    rcases le_total u1 u with h | h
    · exact le_trans (mul_le_mul_of_nonneg_left hsub he) (le_trans (hu1 u h) (le_max_left _ _))
    · have hP1 : (M'.P (Red.ev M' kt B u)).toReal ≤ 1 :=
        ENNReal.toReal_le_of_le_ofReal zero_le_one (by rw [ENNReal.ofReal_one]; exact prob_le_one)
      have hexp : Real.exp (α * u) ≤ Real.exp (α * u1) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left h h1.1)
      calc _ ≤ Real.exp (α * u) * 1 := mul_le_mul_of_nonneg_left hP1 he
        _ ≤ Cb := by rw [mul_one]; exact le_trans hexp (le_max_right _ _)
  -- constants
  set Dt := Dtot.toReal with hDt
  set c2 := M.c2 α with hc2def
  set K1 := 3 * Dt + c1 + Cb + 1 with hK1
  have hK1pos : 0 < K1 := by rw [hK1]; linarith
  set η := ε * c2 / (2 * K1) with hη
  have hηpos : 0 < η := by rw [hη]; positivity
  have hηK1 : η * K1 = ε * c2 / 2 := by rw [hη]; field_simp
  -- the tail of the delay law
  have hlim : ∀ᵐ ω ∂(M.P.restrict {ω | M.T 0 ω ≤ M.Γ ω}),
      Tendsto (fun R : ℕ => {ω | ENNReal.ofReal (R : ℝ) < M.T 0 ω}.indicator
        (fun ω => ENNReal.ofReal (Real.exp (α * (M.T 0 ω).toReal))) ω) atTop (𝓝 0) := by
    refine (ae_restrict_iff' hS0m).mpr (ae_of_all _ fun ω hω => ?_)
    have hT0 : M.T 0 ω ≠ ⊤ := by
      intro h
      have hg := M.T_top 0 ω h
      have hω' : M.T 0 ω ≤ M.Γ ω := hω
      rw [h] at hω'
      exact absurd (top_le_iff.mp hω') (ne_of_lt hg)
    apply tendsto_const_nhds.congr'
    obtain ⟨N, hN⟩ := exists_nat_ge (M.T 0 ω).toReal
    filter_upwards [eventually_ge_atTop N] with R hR
    have : M.T 0 ω ≤ ENNReal.ofReal (R : ℝ) := by
      rw [← ENNReal.ofReal_toReal hT0]
      exact ENNReal.ofReal_le_ofReal (le_trans hN (by exact_mod_cast hR))
    exact (Set.indicator_of_notMem
      (show ω ∉ {ω | ENNReal.ofReal (R : ℝ) < M.T 0 ω} from not_lt.mpr this) _).symm
  have htail := tendsto_lintegral_of_dominated_convergence
    (μ := M.P.restrict {ω | M.T 0 ω ≤ M.Γ ω})
    (F := fun (R : ℕ) ω => {ω | ENNReal.ofReal (R : ℝ) < M.T 0 ω}.indicator
      (fun ω => ENNReal.ofReal (Real.exp (α * (M.T 0 ω).toReal))) ω) (f := fun _ => 0)
    (fun ω => ENNReal.ofReal (Real.exp (α * (M.T 0 ω).toReal)))
    (fun R => hwm.indicator (measurableSet_lt measurable_const (M.measurable_T 0)))
    (fun R => ae_of_all _ fun ω => Set.indicator_le_self _ _ ω) hDtop hlim
  rw [lintegral_zero] at htail
  obtain ⟨R, hR⟩ := ((ENNReal.tendsto_nhds_zero.mp htail) (ENNReal.ofReal η)
    (ENNReal.ofReal_pos.mpr hηpos)).exists
  -- the shifted window function and Theorem (4.2) for the non-delayed version
  obtain ⟨c, hcr, hkc⟩ := hkg
  have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg R
  have hkRmono : MonotoneOn (fun u : ℝ => k (u + R)) (Set.Ici 0) := by
    intro a ha b hb hab
    simp only [Set.mem_Ici] at ha hb
    exact hk (show (0 : ℝ) ≤ a + R by linarith) (show (0 : ℝ) ≤ b + R by linarith)
      (by linarith)
  have hkRg : ∃ c' < M'.rate α, ∀ᶠ u in atTop, ((fun u : ℝ => k (u + R)) u : ℝ) ≤ c' * u := by
    refine ⟨(c + M.rate α) / 2, by rw [hrate]; linarith, ?_⟩
    have h1e := (tendsto_atTop_add_const_right atTop (R : ℝ) tendsto_id).eventually hkc
    have hpos : 0 < (M.rate α - c) / 2 := by linarith
    filter_upwards [h1e, eventually_ge_atTop (c * R / ((M.rate α - c) / 2)),
      eventually_ge_atTop (0 : ℝ)] with u hu hu2 hu0
    simp only [id] at hu
    show (k (u + R) : ℝ) ≤ _
    rw [div_le_iff₀ hpos] at hu2
    nlinarith
  have H42 := uniform_convergence_4_2 M' hreg' h0' h1' h2' h3' h4' h7' (fun u : ℝ => k (u + R))
    hkRmono hkRg η hηpos
  obtain ⟨u0, hu0⟩ := eventually_atTop.mp
    (H42.and (hd'.eventually (Metric.closedBall_mem_nhds c1 hηpos)))
  have H3 := hd.eventually (Metric.closedBall_mem_nhds c2 (show 0 < min η (c2 / 2) by positivity))
  filter_upwards [H3, eventually_ge_atTop (u0 + R), eventually_ge_atTop (0 : ℝ),
    eventually_ge_atTop (R : ℝ)] with t ht3 htu ht0 htR
  intro B hB
  set L := (M.PstarWindow α (k t) B).toReal with hL
  have hL1 : L ≤ 1 :=
    ENNReal.toReal_le_of_le_ofReal zero_le_one (by rw [ENNReal.ofReal_one]; exact hPWle _ B hB)
  have hL0 : 0 ≤ L := ENNReal.toReal_nonneg
  -- uniform-in-delay estimate for delays r ∈ [0, R]
  have hFin : ∀ r : ℝ, 0 ≤ r → r ≤ R →
      |Real.exp (α * (t - r)) * (M'.P (Red.ev M' (k t) B (t - r))).toReal - c1 * L| ≤
        3 * η := by
    intro r hr0 hrR
    have hu0' : u0 ≤ t - r := by linarith
    obtain ⟨hA42, hD2⟩ := hu0 (t - r) hu0'
    have hkK : k t ≤ k (t - r + R) :=
      hk (Set.mem_Ici.mpr ht0) (Set.mem_Ici.mpr (by linarith)) (by linarith)
    have hB'' := hB.preimage (Red.measurable_projP (S := S) (k := k t) (K := k (t - r + R)))
    have hA := hA42 _ hB''
    have hU := hA42 Set.univ MeasurableSet.univ
    rw [hident _ _ hB'', Red.PW_proj' M α hcons (k t) B hB _ hkK] at hA
    rw [hident _ _ MeasurableSet.univ, hPWuniv, ENNReal.toReal_one, mul_one] at hU
    rw [Real.dist_eq] at hD2
    exact Red.core_bound M' hkK B (t - r) (Real.exp (α * (t - r))) c1 L η
      (Real.exp_pos _).le hA hU hD2
  -- integrate against the delay law (delay_shift)
  have hsh := hshift (k t) B hB t ht0
  have hG : ∀ ω, ENNReal.ofReal (Real.exp (α * t)) *
      (if M.T 0 ω ≤ ENNReal.ofReal t then M'.P (Red.ev M' (k t) B (t - (M.T 0 ω).toReal))
        else 0) =
      if M.T 0 ω ≤ ENNReal.ofReal t then
        ENNReal.ofReal (Real.exp (α * (M.T 0 ω).toReal)) *
          ENNReal.ofReal ((fun u => Real.exp (α * u) * (M'.P (Red.ev M' (k t) B u)).toReal)
            (t - (M.T 0 ω).toReal))
      else 0 := by
    intro ω
    split_ifs with hT
    · simp only
      rw [ENNReal.ofReal_mul (Real.exp_pos _).le, ← mul_assoc,
        ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add,
        ENNReal.ofReal_toReal (measure_ne_top _ _)]
      congr 3
      ring
    · rw [mul_zero]
  have hnum := Red.abstract_numer M.P {ω | M.T 0 ω ≤ M.Γ ω} (M.T 0) (M.measurable_T 0) α t R
    (c1 * L) η (3 * η) Cb (fun u => Real.exp (α * u) * (M'.P (Red.ev M' (k t) B u)).toReal)
    (fun ω => ENNReal.ofReal (Real.exp (α * t)) *
      (if M.T 0 ω ≤ ENNReal.ofReal t then M'.P (Red.ev M' (k t) B (t - (M.T 0 ω).toReal))
        else 0))
    hR0 htR hηpos.le (mul_nonneg hc1pos.le hL0) hCb0 hG hFin
    (fun u hu => hFb (k t) B u hu) hDtop hR
  have hGint : ∫⁻ ω in {ω | M.T 0 ω ≤ M.Γ ω}, ENNReal.ofReal (Real.exp (α * t)) *
      (if M.T 0 ω ≤ ENNReal.ofReal t then M'.P (Red.ev M' (k t) B (t - (M.T 0 ω).toReal))
        else 0) ∂M.P = ENNReal.ofReal (Real.exp (α * t)) * M.P (Red.ev M (k t) B t) := by
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    congr 1
    exact hsh.symm
  rw [hGint, ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le] at hnum
  -- the ratio
  have hΓm : MeasurableSet {ω | ENNReal.ofReal t < M.Γ ω} :=
    measurableSet_lt measurable_const (Red.measurable_Γ M)
  rw [ProbabilityTheory.cond_apply hΓm]
  have hset : {ω | ENNReal.ofReal t < M.Γ ω} ∩
      {ω | k t < M.strad t ω ∧ (M.win (k t) t ω, M.age t ω) ∈ B} = Red.ev M (k t) B t := by
    ext ω
    simp only [Red.ev, Set.mem_inter_iff, Set.mem_ofPred_eq]
    tauto
  rw [hset, ENNReal.toReal_mul, ENNReal.toReal_inv]
  set p := (M.P {ω | ENNReal.ofReal t < M.Γ ω}).toReal with hp
  set q := (M.P (Red.ev M (k t) B t)).toReal with hq
  set e := Real.exp (α * t) with he
  rw [Real.dist_eq] at ht3
  have ht3' := abs_le.mp ht3
  have hmin1 : min η (c2 / 2) ≤ η := min_le_left _ _
  have hmin2 : min η (c2 / 2) ≤ c2 / 2 := min_le_right _ _
  have hep : c2 / 2 ≤ e * p := by linarith [ht3'.1]
  have hep0 : 0 < e * p := by linarith
  have hepos : 0 < e := Real.exp_pos _
  have hppos : 0 < p := by
    by_contra hneg
    push_neg at hneg
    have := mul_nonpos_of_nonneg_of_nonpos hepos.le hneg
    linarith
  have hnum' := abs_le.mp hnum
  have hc2' : c2 = Dt * c1 := hc2eq
  have k1 := mul_le_mul_of_nonneg_left (show e * p - c2 ≤ η by linarith [ht3'.2]) hL0
  have k2 := mul_le_mul_of_nonneg_left (show -η ≤ e * p - c2 by linarith [ht3'.1]) hL0
  have k3 := mul_le_mul_of_nonneg_left hL1 (mul_nonneg hc1pos.le hηpos.le)
  have k4 := mul_le_mul_of_nonneg_left hL1 hηpos.le
  have k5 := mul_le_mul_of_nonneg_left hep hε.le
  have hLc2 : L * c2 = c1 * L * Dt := by rw [hc2']; ring
  have hηK1' : 3 * η * Dt + c1 * η + Cb * η + η = ε * c2 / 2 := by rw [← hηK1, hK1]; ring
  have k6 : L * (e * p) = L * c2 + L * (e * p - c2) := by ring
  have key : |e * q - L * (e * p)| ≤ ε * (e * p) := by
    rw [abs_le]
    constructor
    · linarith [hnum'.1, k1, k3, k4, k5, k6, hLc2, hηK1']
    · linarith [hnum'.2, k2, k3, k4, k5, k6, hLc2, hηK1']
  have hrw : p⁻¹ * q - L = (e * q - L * (e * p)) / (e * p) := by
    field_simp
  rw [hrw, abs_div, abs_of_pos hep0, div_le_iff₀ hep0]
  exact key
