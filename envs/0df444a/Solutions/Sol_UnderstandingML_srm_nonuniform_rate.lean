-- Prove2me | solution 1 for UnderstandingML.srm_nonuniform_rate
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-25T14:09:23.705759+00:00
-- url     : https://prove2.me/submissions/d1e759f6-977a-42e0-8f6c-3d862d7b320a

import Definitions.Def_UnderstandingML_Nonuniform
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.NumberTheory.ZetaValues

open MeasureTheory

namespace UnderstandingML

/-- A decreasing sequence in the set of Equation (7.1) converging to its infimum from above. -/
theorem srmAux_exists_antitone_seq (T : Set ℝ) (hT : T.Nonempty) :
    ∃ f : ℕ → ℝ, (∀ k, f k ∈ T) ∧ Antitone f ∧ ∀ k, f k < sInf T + 1 / ((k : ℝ) + 1) := by
  have he : ∀ k : ℕ, ∃ e ∈ T, e < sInf T + 1 / ((k : ℝ) + 1) := fun k =>
    exists_lt_of_csInf_lt hT (by have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
                                 linarith)
  choose e heT hel using he
  let f : ℕ → ℝ := fun k => Nat.rec (e 0) (fun j fj => min fj (e (j + 1))) k
  have hf0 : f 0 = e 0 := rfl
  have hfs : ∀ j, f (j + 1) = min (f j) (e (j + 1)) := fun _ => rfl
  refine ⟨f, ?_, ?_, ?_⟩
  · intro k
    induction k with
    | zero => exact heT 0
    | succ j ih =>
      rw [hfs]
      rcases min_choice (f j) (e (j + 1)) with h | h <;> rw [h]
      · exact ih
      · exact heT _
  · refine antitone_nat_of_succ_le fun j => ?_
    rw [hfs]; exact min_le_left _ _
  · intro k
    have : f k ≤ e k := by
      cases k with
      | zero => exact le_of_eq hf0
      | succ j => rw [hfs]; exact min_le_right _ _
    exact lt_of_le_of_lt this (hel k)

/-- **Theorem 7.4 for a single index.** If `H` has the uniform convergence property with `mUC`,
`η ∈ (0,1)` and `ε(m, η)` of Equation (7.1) is defined, then with probability at least `1 − η`
every `h ∈ H` has `|L_D(h) − L_S(h)| ≤ ε(m, η)`. -/
theorem srmAux_single_index {Z : Type*} [MeasurableSpace Z] {Hyp : Type*}
    (loss : Hyp → Z → ℝ) (H : Set Hyp) (mUC : ℝ → ℝ → ℕ)
    (hUC : HasUniformConvergenceWith loss H mUC) {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1)
    (D : Measure Z) [IsProbabilityMeasure D] (m : ℕ) (hdef : RateDefined mUC m η) :
    iidLaw D m {S | ∃ h ∈ H, epsRate mUC m η < |risk loss D h - empRisk loss S h|} ≤
      ENNReal.ofReal η := by
  set T : Set ℝ := {ε : ℝ | 0 < ε ∧ ε < 1 ∧ mUC ε η ≤ m} with hTdef
  have hTne : T.Nonempty := hdef
  obtain ⟨f, hfT, hfanti, hflt⟩ := srmAux_exists_antitone_seq T hTne
  set E : ℕ → Set (Fin m → Z) := fun k => {S | ¬ IsRepresentative loss H D (f k) S}
  have hEmono : Monotone E := by
    intro i j hij S hS
    simp only [E, Set.mem_setOf_eq, IsRepresentative, not_forall] at hS ⊢
    obtain ⟨h, hh, hlt⟩ := hS
    exact ⟨h, hh, fun hle => hlt (hle.trans (hfanti hij))⟩
  have hsub : {S : Fin m → Z | ∃ h ∈ H, epsRate mUC m η < |risk loss D h - empRisk loss S h|}
      ⊆ ⋃ k, E k := by
    rintro S ⟨h, hh, hlt⟩
    have hpos : 0 < |risk loss D h - empRisk loss S h| - epsRate mUC m η := by linarith
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hpos
    refine Set.mem_iUnion.2 ⟨k, ?_⟩
    simp only [E, Set.mem_setOf_eq, IsRepresentative, not_forall]
    refine ⟨h, hh, fun hle => ?_⟩
    rw [abs_sub_comm] at hle
    have := hflt k
    simp only [epsRate] at hk
    linarith
  calc iidLaw D m {S | ∃ h ∈ H, epsRate mUC m η < |risk loss D h - empRisk loss S h|}
      ≤ iidLaw D m (⋃ k, E k) := measure_mono hsub
    _ = ⨆ k, iidLaw D m (E k) := hEmono.measure_iUnion
    _ ≤ ENNReal.ofReal η := by
      refine iSup_le fun k => ?_
      obtain ⟨h0, h1, hm⟩ := hfT k
      exact hUC (f k) η h0 h1 hη0 hη1 D inferInstance m hm

/-- The weighted union bound: Theorem 7.4 with the pieces as given. -/
theorem srmAux_bound {Z : Type*} [MeasurableSpace Z] {Hyp : Type*} (loss : Hyp → Z → ℝ)
    (Hn : ℕ → Set Hyp) (mUC : ℕ → ℝ → ℝ → ℕ)
    (hUC : ∀ n, HasUniformConvergenceWith loss (Hn n) (mUC n)) (w : ℕ → ℝ)
    (hw : ∀ n, 0 ≤ w n ∧ w n ≤ 1) (hsum : ∀ N, ∑ n ∈ Finset.range N, w n ≤ 1) {δ : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (D : Measure Z) [IsProbabilityMeasure D] (m : ℕ) :
    iidLaw D m {S | ∃ n, 0 < w n ∧ RateDefined (mUC n) m (w n * δ) ∧
        ∃ h ∈ Hn n, epsRate (mUC n) m (w n * δ) < |risk loss D h - empRisk loss S h|} ≤
      ENNReal.ofReal δ := by
  classical
  set F : ℕ → Set (Fin m → Z) := fun n =>
    {S | 0 < w n ∧ RateDefined (mUC n) m (w n * δ) ∧
        ∃ h ∈ Hn n, epsRate (mUC n) m (w n * δ) < |risk loss D h - empRisk loss S h|}
  have hsub : {S : Fin m → Z | ∃ n, 0 < w n ∧ RateDefined (mUC n) m (w n * δ) ∧
        ∃ h ∈ Hn n, epsRate (mUC n) m (w n * δ) < |risk loss D h - empRisk loss S h|}
      = ⋃ n, F n := by
    ext S; simp [F]
  have hF : ∀ n, iidLaw D m (F n) ≤ ENNReal.ofReal (w n) * ENNReal.ofReal δ := by
    intro n
    by_cases hc : 0 < w n ∧ RateDefined (mUC n) m (w n * δ)
    · have hη0 : 0 < w n * δ := mul_pos hc.1 hδ0
      have hη1 : w n * δ < 1 := by nlinarith [(hw n).2]
      calc iidLaw D m (F n)
          ≤ iidLaw D m {S | ∃ h ∈ Hn n,
              epsRate (mUC n) m (w n * δ) < |risk loss D h - empRisk loss S h|} :=
            measure_mono fun S hS => hS.2.2
        _ ≤ ENNReal.ofReal (w n * δ) :=
            srmAux_single_index loss (Hn n) (mUC n) (hUC n) hη0 hη1 D m hc.2
        _ = ENNReal.ofReal (w n) * ENNReal.ofReal δ := ENNReal.ofReal_mul (hw n).1
    · have : F n = ∅ := by
        ext S; simp only [F, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        exact fun h => hc ⟨h.1, h.2.1⟩
      rw [this, measure_empty]; positivity
  have htsum : ∑' n, ENNReal.ofReal (w n) ≤ 1 := by
    refine ENNReal.tsum_le_of_sum_range_le fun N => ?_
    rw [← ENNReal.ofReal_sum_of_nonneg fun n _ => (hw n).1]
    exact ENNReal.ofReal_le_one.2 (hsum N)
  calc iidLaw D m _ = iidLaw D m (⋃ n, F n) := by rw [hsub]
    _ ≤ ∑' n, iidLaw D m (F n) := measure_iUnion_le _
    _ ≤ ∑' n, ENNReal.ofReal (w n) * ENNReal.ofReal δ := ENNReal.tsum_le_tsum hF
    _ = (∑' n, ENNReal.ofReal (w n)) * ENNReal.ofReal δ := ENNReal.tsum_mul_right
    _ ≤ 1 * ENNReal.ofReal δ := by gcongr
    _ = ENNReal.ofReal δ := one_mul _


/-- The weights `w(n) = 6/(π² n²)` lie in `[0,1]`. -/
theorem srmAux_weight_mem (n : ℕ) : 0 ≤ srmWeight n ∧ srmWeight n ≤ 1 := by
  unfold srmWeight
  refine ⟨by positivity, ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hpi : 9 < Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
    have hn1 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith
    rw [div_le_one (by positivity)]
    nlinarith

/-- The partial sums of `w(n) = 6/(π² n²)` are at most `1` (Basel problem). -/
theorem srmAux_weight_sum (N : ℕ) : ∑ n ∈ Finset.range N, srmWeight n ≤ 1 := by
  have hpi : 0 < Real.pi ^ 2 := by positivity
  have h := sum_le_hasSum (Finset.range N) (fun i _ => by positivity) hasSum_zeta_two
  have : ∑ n ∈ Finset.range N, srmWeight n =
      6 / Real.pi ^ 2 * ∑ n ∈ Finset.range N, 1 / (n : ℝ) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    unfold srmWeight
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      field_simp
  rw [this]
  calc 6 / Real.pi ^ 2 * ∑ n ∈ Finset.range N, 1 / (n : ℝ) ^ 2
      ≤ 6 / Real.pi ^ 2 * (Real.pi ^ 2 / 6) := by gcongr
    _ = 1 := by field_simp

/-- The first index of a member of `⋃ₙ Hₙ` contains it. -/
theorem srmAux_mem_firstIndex {Hyp : Type*} (Hn : ℕ → Set Hyp) {h : Hyp}
    (hh : h ∈ ⋃ n, Hn n) : h ∈ Hn (firstIndex Hn h) := by
  obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hh
  exact Nat.sInf_mem (s := {n | h ∈ Hn n}) ⟨n, hn⟩

/-- `ε(m, η)` is at most any member of the set of Equation (7.1). -/
theorem srmAux_epsRate_le {mUC : ℝ → ℝ → ℕ} {m : ℕ} {η ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1)
    (hm : mUC ε η ≤ m) : epsRate mUC m η ≤ ε :=
  csInf_le ⟨0, fun _ hx => hx.1.le⟩ ⟨h0, h1, hm⟩

/-- **Theorem 7.5.** -/
theorem srmAux_nonuniform_rate {Z : Type*} [MeasurableSpace Z] {Hyp : Type*}
    (loss : Hyp → Z → ℝ) (Hn : ℕ → Set Hyp) (h0 : Hn 0 = ∅) (mUC : ℕ → ℝ → ℝ → ℕ)
    (hUC : ∀ n, HasUniformConvergenceWith loss (Hn n) (mUC n)) (A : ℝ → Learner Z Hyp)
    (hA : IsSRMFamily loss Hn mUC srmWeight A) :
    IsNonuniformFamilyWith loss (⋃ n, Hn n) A fun ε δ h ↦
      mUC (firstIndex Hn h) (ε / 2) (6 * δ / (Real.pi * firstIndex Hn h) ^ 2) := by
  refine ⟨hA.1, ?_⟩
  intro ε δ hε0 hε1 hδ0 hδ1 h hh D hD m hm
  set k := firstIndex Hn h with hkdef
  have hhk : h ∈ Hn k := srmAux_mem_firstIndex Hn hh
  have hk0 : k ≠ 0 := by
    intro hk; rw [hk, h0] at hhk; exact hhk
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk0
  have hwk : srmWeight k * δ = 6 * δ / (Real.pi * k) ^ 2 := by
    unfold srmWeight; field_simp
  have hwpos : 0 < srmWeight k := by unfold srmWeight; positivity
  have hm' : mUC k (ε / 2) (srmWeight k * δ) ≤ m := by rw [hwk]; exact hm
  have hrate : RateDefined (mUC k) m (srmWeight k * δ) :=
    ⟨ε / 2, by linarith, by linarith, hm'⟩
  have hadm : Admissible Hn mUC srmWeight δ m h := ⟨hh, hwpos, hrate⟩
  have hepsk : epsRate (mUC k) m (srmWeight k * δ) ≤ ε / 2 :=
    srmAux_epsRate_le (by linarith) (by linarith) hm'
  refine le_trans (measure_mono ?_) (srmAux_bound loss Hn mUC hUC srmWeight srmAux_weight_mem
    srmAux_weight_sum hδ0 hδ1 D m)
  intro S hS
  simp only [Set.mem_setOf_eq] at hS ⊢
  by_contra hgood
  push_neg at hgood
  obtain ⟨hadm', hmin⟩ := hA.2 δ hδ0 hδ1 m S ⟨h, hadm⟩
  set h' := A δ m S
  obtain ⟨hh', hw', hrate'⟩ := hadm'
  have hh'k : h' ∈ Hn (firstIndex Hn h') := srmAux_mem_firstIndex Hn hh'
  have e1 := hgood _ hw' hrate' h' hh'k
  have e2 := hgood k hwpos hrate h hhk
  have hobj := hmin h hadm
  simp only [srmObjective] at hobj
  rw [← hkdef] at hobj
  have a1 := (abs_le.1 e1).2
  have a2 := (abs_le.1 e2).1
  linarith

end UnderstandingML

/-- **Theorem 7.5** (p. 87). -/
theorem solution {Z : Type*} [MeasurableSpace Z] {Hyp : Type*} (loss : Hyp → Z → ℝ)
    (Hn : ℕ → Set Hyp) (h0 : Hn 0 = ∅) (mUC : ℕ → ℝ → ℝ → ℕ)
    (hUC : ∀ n, UnderstandingML.HasUniformConvergenceWith loss (Hn n) (mUC n))
    (A : ℝ → UnderstandingML.Learner Z Hyp)
    (hA : UnderstandingML.IsSRMFamily loss Hn mUC UnderstandingML.srmWeight A) :
    UnderstandingML.IsNonuniformFamilyWith loss (⋃ n, Hn n) A fun ε δ h ↦
      mUC (UnderstandingML.firstIndex Hn h) (ε / 2)
        (6 * δ / (Real.pi * UnderstandingML.firstIndex Hn h) ^ 2) :=
  UnderstandingML.srmAux_nonuniform_rate loss Hn h0 mUC hUC A hA
