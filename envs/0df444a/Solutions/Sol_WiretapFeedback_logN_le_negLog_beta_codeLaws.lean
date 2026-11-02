-- Prove2me | solution 1 for WiretapFeedback.logN_le_negLog_beta_codeLaws
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-02T05:45:20.555427+00:00
-- url     : https://prove2.me/submissions/ae136220-0101-485c-bd06-ee0d0b6e98a1

import Mathlib
import Definitions.Def_WiretapFeedback_negLog2
import Definitions.Def_WiretapFeedback_tvDist
import Definitions.Def_WiretapFeedback_testBeta
import Definitions.Def_WiretapFeedback_IsWiretapCode
import Definitions.Def_WiretapFeedback_WiretapCode_law
import Theorems.Thm_WiretapFeedback_condIndep_message_decoded

open scoped ENNReal

namespace SKAux

open WiretapFeedback

/-! ### Marginals of a law on `A × B × C` -/

section Marginals

variable {A B C : Type}

lemma map_snd_snd_apply (P : PMF (A × B × C)) (c : C) :
    (P.map fun t => t.2.2) c = ∑' a, ∑' b, P (a, b, c) := by
  classical
  rw [PMF.map_apply, ENNReal.tsum_prod']
  refine tsum_congr fun a => ?_
  rw [ENNReal.tsum_prod']
  refine tsum_congr fun b => ?_
  rw [tsum_eq_single c]
  · simp
  · intro c' hc'; rw [if_neg]; intro h; exact hc' h.symm

lemma map_fst_snd_apply (P : PMF (A × B × C)) (a : A) (c : C) :
    (P.map fun t => (t.1, t.2.2)) (a, c) = ∑' b, P (a, b, c) := by
  classical
  rw [PMF.map_apply, ENNReal.tsum_prod', tsum_eq_single a]
  · rw [ENNReal.tsum_prod']
    refine tsum_congr fun b => ?_
    rw [tsum_eq_single c]
    · simp
    · intro c' hc'; rw [if_neg]; intro h; exact hc' (congrArg Prod.snd h).symm
  · intro a' ha'
    refine ENNReal.tsum_eq_zero.mpr fun bc => ?_
    rw [if_neg]; intro h; exact ha' (congrArg Prod.fst h).symm

lemma map_snd_fst_apply (P : PMF (A × B × C)) (b : B) (c : C) :
    (P.map fun t => (t.2.1, t.2.2)) (b, c) = ∑' a, P (a, b, c) := by
  classical
  rw [PMF.map_apply, ENNReal.tsum_prod']
  refine tsum_congr fun a => ?_
  rw [ENNReal.tsum_prod', tsum_eq_single b]
  · rw [tsum_eq_single c]
    · simp
    · intro c' hc'; rw [if_neg]; intro h; exact hc' (congrArg Prod.snd h).symm
  · intro b' hb'
    refine ENNReal.tsum_eq_zero.mpr fun c' => ?_
    rw [if_neg]; intro h; exact hb' (congrArg Prod.fst h).symm

end Marginals

/-! ### Variation distance -/

lemma tsum_tsub_eq {α : Type} (P R : PMF α) :
    ∑' a, (P a - R a) = ∑' a, (R a - P a) := by
  have h1 : ∑' a, P a = ∑' a, min (P a) (R a) + ∑' a, (P a - R a) := by
    rw [← ENNReal.tsum_add]
    refine tsum_congr fun a => ?_
    rw [add_comm, tsub_add_min]
  have h2 : ∑' a, R a = ∑' a, min (P a) (R a) + ∑' a, (R a - P a) := by
    rw [← ENNReal.tsum_add]
    refine tsum_congr fun a => ?_
    rw [add_comm, min_comm, tsub_add_min]
  rw [P.tsum_coe] at h1
  rw [R.tsum_coe] at h2
  have hfin : ∑' a, min (P a) (R a) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
    rw [← P.tsum_coe]
    exact ENNReal.tsum_le_tsum fun a => min_le_left _ _
  exact (ENNReal.add_right_inj hfin).mp (h1.symm.trans h2)

lemma tvDist_eq {α : Type} (P R : PMF α) : tvDist P R = ∑' a, (P a - R a) := by
  unfold tvDist
  rw [ENNReal.tsum_add, ← tsum_tsub_eq, ← two_mul, ← mul_assoc,
    ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]

/-- `P[g] ≤ R[g] + ‖P − R‖` for a `[0,1]`-valued `g`. -/
lemma tsum_le_add_tvDist {α : Type} (P R : PMF α) (g : α → ℝ≥0∞) (hg : ∀ a, g a ≤ 1) :
    ∑' a, P a * g a ≤ ∑' a, R a * g a + tvDist P R := by
  rw [tvDist_eq, ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun a => ?_
  calc P a * g a ≤ (R a + (P a - R a)) * g a := by
        gcongr; exact le_add_tsub
    _ = R a * g a + (P a - R a) * g a := add_mul _ _ _
    _ ≤ R a * g a + (P a - R a) := by
        gcongr
        calc (P a - R a) * g a ≤ (P a - R a) * 1 := by gcongr; exact hg a
          _ = P a - R a := mul_one _

/-! ### Indicator sums and pushforwards -/

lemma tsum_indicator_map {α β : Type} (p : PMF α) (f : α → β) (S : Set β) :
    ∑' b, (p.map f) b * S.indicator 1 b = ∑' a, p a * S.indicator 1 (f a) := by
  have h1 : ∀ (q : PMF β), ∑' b, q b * S.indicator 1 b = q.toOuterMeasure S := by
    intro q
    rw [PMF.toOuterMeasure_apply]
    refine tsum_congr fun b => ?_
    by_cases hb : b ∈ S <;> simp [hb]
  have h2 : ∑' a, p a * S.indicator 1 (f a) = p.toOuterMeasure (f ⁻¹' S) := by
    rw [PMF.toOuterMeasure_apply]
    refine tsum_congr fun a => ?_
    by_cases ha : f a ∈ S <;> simp [ha, Set.indicator, Set.mem_preimage]
  rw [h1, h2, PMF.toOuterMeasure_map_apply]

/-! ### The one-shot bound -/

section OneShot

variable {Z' : Type} {k : ℕ}

/-- Type-II error of the test `T = 1{a = b, Q_{B|Z}(a|z) ≤ L}`. -/
lemma Q_bound (Q : PMF (Fin k × Fin k × Z'))
    (hQ : ∀ (a b : Fin k) (z : Z'), Q (a, b, z) * (Q.map fun t => t.2.2) z =
        (Q.map fun t => (t.1, t.2.2)) (a, z) * (Q.map fun t => (t.2.1, t.2.2)) (b, z))
    (L : ℝ≥0∞) :
    ∑' t : Fin k × Fin k × Z', Q t *
      (if t.1 = t.2.1 ∧ (Q.map fun t => (t.2.1, t.2.2)) (t.1, t.2.2) ≤
        L * (Q.map fun t => t.2.2) t.2.2 then 1 else 0) ≤ L := by
  classical
  set QZ := Q.map fun t => t.2.2 with hQZ
  set QA := Q.map fun t => (t.1, t.2.2) with hQA
  set QB := Q.map fun t => (t.2.1, t.2.2) with hQB
  rw [ENNReal.tsum_prod']
  -- pointwise bound
  have hpt : ∀ a z, Q (a, a, z) * (if QB (a, z) ≤ L * QZ z then 1 else 0) ≤ L * QA (a, z) := by
    intro a z
    split_ifs with hgood
    · rw [mul_one]
      by_cases hz : QZ z = 0
      · have : Q (a, a, z) ≤ QZ z := by
          rw [hQZ, map_snd_snd_apply]
          exact (ENNReal.le_tsum a).trans' (ENNReal.le_tsum (f := fun b => Q (a, b, z)) a)
        rw [hz] at this
        rw [nonpos_iff_eq_zero.mp this]
        exact zero_le
      · have hfin : QZ z ≠ ⊤ := PMF.apply_ne_top _ _
        rw [← ENNReal.mul_le_mul_iff_left hz hfin, hQ a a z]
        calc QA (a, z) * QB (a, z) ≤ QA (a, z) * (L * QZ z) := by gcongr
          _ = L * QA (a, z) * QZ z := by ring
    · rw [mul_zero]; exact zero_le
  calc ∑' a, ∑' bz : Fin k × Z', Q (a, bz) * (if (a, bz).1 = (a, bz).2.1 ∧
          QB ((a, bz).1, (a, bz).2.2) ≤ L * QZ (a, bz).2.2 then 1 else 0)
      = ∑' a, ∑' z, Q (a, a, z) * (if QB (a, z) ≤ L * QZ z then 1 else 0) := by
        refine tsum_congr fun a => ?_
        rw [ENNReal.tsum_prod', tsum_eq_single a]
        · simp
        · intro b hb
          refine ENNReal.tsum_eq_zero.mpr fun z => ?_
          simp [Ne.symm hb]
    _ ≤ ∑' a, ∑' z, L * QA (a, z) := ENNReal.tsum_le_tsum fun a => ENNReal.tsum_le_tsum fun z => hpt a z
    _ = L := by
        simp_rw [ENNReal.tsum_mul_left]
        rw [← ENNReal.tsum_prod' (f := fun p : Fin k × Z' => QA p), PMF.tsum_coe, mul_one]

/-- The number of "bad" keys for a fixed `z` is at most `k η`. -/
lemma count_bound (Q : PMF (Fin k × Fin k × Z')) (η : ℝ) (hη : 0 < η) (hk : 0 < k) (z : Z') :
    (k : ℝ≥0∞)⁻¹ * ∑ a : Fin k, {p : Fin k × Z' | ¬ (Q.map fun t => (t.2.1, t.2.2)) p ≤
      ENNReal.ofReal (1 / (k * η)) * (Q.map fun t => t.2.2) p.2}.indicator 1 (a, z) ≤
      ENNReal.ofReal η := by
  classical
  set QZ := Q.map fun t => t.2.2 with hQZ
  set QB := Q.map fun t => (t.2.1, t.2.2) with hQB
  set L := ENNReal.ofReal (1 / (k * η)) with hL
  have hkη : (0 : ℝ) < k * η := mul_pos (by exact_mod_cast hk) hη
  have hQBle : ∀ a, QB (a, z) ≤ QZ z := by
    intro a
    rw [hQB, map_snd_fst_apply, hQZ, map_snd_snd_apply]
    exact ENNReal.tsum_le_tsum fun a' => ENNReal.le_tsum (f := fun b => Q (a', b, z)) a
  have hsumQB : ∑ a : Fin k, QB (a, z) = QZ z := by
    have e : ∑ a : Fin k, QB (a, z) = ∑' a, QB (a, z) := (tsum_fintype _).symm
    rw [e]
    simp only [hQB, map_snd_fst_apply]
    rw [hQZ, map_snd_snd_apply]
    exact ENNReal.tsum_comm
  set cz : ℝ≥0∞ := ∑ a : Fin k,
    {p : Fin k × Z' | ¬ QB p ≤ L * QZ p.2}.indicator (1 : Fin k × Z' → ℝ≥0∞) (a, z) with hcz
  by_cases hz : QZ z = 0
  · have : cz = 0 := by
      refine Finset.sum_eq_zero fun a _ => ?_
      have h0 : QB (a, z) = 0 := nonpos_iff_eq_zero.mp (hz ▸ hQBle a)
      simp [Set.indicator, h0]
    rw [this, mul_zero]; exact zero_le
  · have hfin : QZ z ≠ ⊤ := PMF.apply_ne_top _ _
    have h1 : cz * (L * QZ z) ≤ QZ z := by
      rw [hcz, Finset.sum_mul]
      conv_rhs => rw [← hsumQB]
      refine Finset.sum_le_sum fun a _ => ?_
      by_cases hb : ¬ QB (a, z) ≤ L * QZ z
      · rw [Set.indicator_of_mem (show (a, z) ∈ {p : Fin k × Z' | ¬ QB p ≤ L * QZ p.2} from hb),
          Pi.one_apply, one_mul]
        exact (not_le.mp hb).le
      · rw [Set.indicator_of_notMem (show (a, z) ∉ {p : Fin k × Z' | ¬ QB p ≤ L * QZ p.2} from hb),
          zero_mul]
        exact zero_le
    have h2 : cz * L ≤ 1 := by
      rw [← ENNReal.mul_le_mul_iff_left hz hfin, one_mul, mul_assoc]
      exact h1
    have h3 : cz ≤ ENNReal.ofReal (k * η) := by
      have := ENNReal.le_inv_iff_mul_le.mpr h2
      rwa [hL, ← ENNReal.ofReal_inv_of_pos (by positivity), one_div, inv_inv] at this
    calc (k : ℝ≥0∞)⁻¹ * cz ≤ (k : ℝ≥0∞)⁻¹ * ENNReal.ofReal (k * η) := by gcongr
      _ = ENNReal.ofReal η := by
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_inv_of_pos (by exact_mod_cast hk),
          ← ENNReal.ofReal_mul (by positivity), ← mul_assoc, inv_mul_cancel₀ (by positivity),
          one_mul]

/-- Type-I error of the test: `P[T] ≥ 1 − ε − δ − η`. -/
lemma P_bound [NeZero k] (P Q : PMF (Fin k × Fin k × Z')) (ε δ η : ℝ) (hε : 0 ≤ ε) (hδ : 0 ≤ δ)
    (hη : 0 < η)
    (hP_err : P.toOuterMeasure {t | t.1 ≠ t.2.1} ≤ ENNReal.ofReal ε)
    (hP_sec : tvDist (P.map fun t => (t.1, t.2.2))
        ((PMF.uniformOfFintype (Fin k)).bind fun a => (P.map fun t => t.2.2).map fun z => (a, z))
      ≤ ENNReal.ofReal δ) :
    ENNReal.ofReal (1 - (ε + δ + η)) ≤ ∑' t : Fin k × Fin k × Z', P t *
      (if t.1 = t.2.1 ∧ (Q.map fun t => (t.2.1, t.2.2)) (t.1, t.2.2) ≤
        ENNReal.ofReal (1 / (k * η)) * (Q.map fun t => t.2.2) t.2.2 then 1 else 0) := by
  classical
  have hk : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  set QZ := Q.map fun t => t.2.2 with hQZ
  set QB := Q.map fun t => (t.2.1, t.2.2) with hQB
  set L := ENNReal.ofReal (1 / (k * η)) with hL
  set T : Fin k × Fin k × Z' → ℝ≥0∞ := fun t =>
    if t.1 = t.2.1 ∧ QB (t.1, t.2.2) ≤ L * QZ t.2.2 then 1 else 0 with hT
  set Bad : Set (Fin k × Z') := {p | ¬ QB p ≤ L * QZ p.2} with hBad
  set E : Set (Fin k × Fin k × Z') := {t | t.1 ≠ t.2.1} with hE
  set PZ := P.map fun t => t.2.2 with hPZ
  set PAZ := P.map fun t => (t.1, t.2.2) with hPAZ
  set R := (PMF.uniformOfFintype (Fin k)).bind fun a => PZ.map fun z => (a, z) with hR
  -- pointwise cover
  have hcover : ∀ t, P t ≤ P t * T t + P t * E.indicator 1 t +
      P t * Bad.indicator 1 (t.1, t.2.2) := by
    intro t
    by_cases h1 : t.1 = t.2.1
    · by_cases h2 : QB (t.1, t.2.2) ≤ L * QZ t.2.2
      · have : T t = 1 := if_pos ⟨h1, h2⟩
        rw [this, mul_one, add_assoc]; exact le_self_add
      · have : Bad.indicator (1 : Fin k × Z' → ℝ≥0∞) (t.1, t.2.2) = 1 := by
          simp [hBad, Set.indicator, h2]
        rw [this, mul_one]; exact le_add_self
    · have : E.indicator (1 : Fin k × Fin k × Z' → ℝ≥0∞) t = 1 := by
        simp [hE, Set.indicator, h1]
      rw [this, mul_one]
      exact (le_add_self).trans (le_self_add)
  have hsum := ENNReal.tsum_le_tsum hcover
  rw [P.tsum_coe, ENNReal.tsum_add, ENNReal.tsum_add] at hsum
  -- the reliability term
  have hE' : ∑' t, P t * E.indicator 1 t ≤ ENNReal.ofReal ε := by
    refine le_trans (le_of_eq ?_) hP_err
    rw [PMF.toOuterMeasure_apply]
    refine tsum_congr fun t => ?_
    by_cases ht : t ∈ E <;> simp [ht]
  -- the secrecy term
  have hR_apply : ∀ a z, R (a, z) = (k : ℝ≥0∞)⁻¹ * PZ z := by
    intro a z
    rw [hR, PMF.bind_apply, tsum_eq_single a]
    · rw [PMF.map_apply, tsum_eq_single z]
      · simp [PMF.uniformOfFintype_apply]
      · intro z' hz'; rw [if_neg]; intro h; exact hz' (congrArg Prod.snd h).symm
    · intro a' ha'
      refine mul_eq_zero_of_right _ ?_
      rw [PMF.map_apply]
      exact ENNReal.tsum_eq_zero.mpr fun z' => if_neg (fun h => ha' (congrArg Prod.fst h).symm)
  have hRbad : ∑' p, R p * Bad.indicator 1 p ≤ ENNReal.ofReal η := by
    rw [ENNReal.tsum_prod', ENNReal.tsum_comm]
    simp only [hR_apply]
    calc ∑' z, ∑' a : Fin k, (k : ℝ≥0∞)⁻¹ * PZ z * Bad.indicator 1 (a, z)
        = ∑' z, PZ z * ((k : ℝ≥0∞)⁻¹ * ∑ a : Fin k, Bad.indicator 1 (a, z)) := by
          refine tsum_congr fun z => ?_
          rw [tsum_fintype, Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ => ?_
          ring
      _ ≤ ∑' z, PZ z * ENNReal.ofReal η := by
          refine ENNReal.tsum_le_tsum fun z => ?_
          gcongr
          exact count_bound Q η hη hk z
      _ = ENNReal.ofReal η := by rw [ENNReal.tsum_mul_right, PZ.tsum_coe, one_mul]
  have hBad' : ∑' t, P t * Bad.indicator 1 (t.1, t.2.2) ≤ ENNReal.ofReal η + ENNReal.ofReal δ := by
    rw [← tsum_indicator_map P (fun t => (t.1, t.2.2)) Bad]
    refine (tsum_le_add_tvDist PAZ R _ ?_).trans ?_
    · intro p; by_cases hp : p ∈ Bad <;> simp [hp]
    · exact add_le_add hRbad hP_sec
  -- assemble
  have htot : 1 ≤ ∑' t, P t * T t + ENNReal.ofReal (ε + δ + η) := by
    refine hsum.trans ?_
    rw [ENNReal.ofReal_add (by positivity) hη.le, ENNReal.ofReal_add hε hδ]
    calc ∑' t, P t * T t + ∑' t, P t * E.indicator 1 t + ∑' t, P t * Bad.indicator 1 (t.1, t.2.2)
        ≤ ∑' t, P t * T t + ENNReal.ofReal ε + (ENNReal.ofReal η + ENNReal.ofReal δ) := by
          gcongr
      _ = ∑' t, P t * T t + (ENNReal.ofReal ε + ENNReal.ofReal δ + ENNReal.ofReal η) := by ring
  rw [ENNReal.ofReal_sub _ (by positivity), ENNReal.ofReal_one]
  exact tsub_le_iff_right.mpr htot

end OneShot

end SKAux

open SKAux in
theorem sk_bound {Z' : Type} (k : ℕ) [NeZero k] (ε δ η : ℝ) (hε : 0 ≤ ε)
    (hδ : 0 ≤ δ) (hεδ : ε + δ < 1) (P Q : PMF (Fin k × Fin k × Z'))
    (hP_err : P.toOuterMeasure {t | t.1 ≠ t.2.1} ≤ ENNReal.ofReal ε)
    (hP_sec : WiretapFeedback.tvDist (P.map fun t => (t.1, t.2.2))
        ((PMF.uniformOfFintype (Fin k)).bind fun a => (P.map fun t => t.2.2).map fun z => (a, z))
      ≤ ENNReal.ofReal δ)
    (hQ : ∀ (a b : Fin k) (z : Z'), Q (a, b, z) * (Q.map fun t => t.2.2) z =
        (Q.map fun t => (t.1, t.2.2)) (a, z) * (Q.map fun t => (t.2.1, t.2.2)) (b, z))
    (hη0 : 0 < η) (hη1 : η < 1 - ε - δ) :
    ((Real.logb 2 k : ℝ) : EReal) ≤
      WiretapFeedback.negLog2 (WiretapFeedback.testBeta (ε + δ + η) P Q) +
        ((2 * Real.logb 2 (1 / η) : ℝ) : EReal) := by
  classical
  have hk : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  have hkη : (0 : ℝ) < k * η := mul_pos (by exact_mod_cast hk) hη0
  set L := ENNReal.ofReal (1 / (k * η)) with hL
  -- the test
  have hβ : WiretapFeedback.testBeta (ε + δ + η) P Q ≤ L := by
    unfold WiretapFeedback.testBeta
    refine iInf_le_of_le (fun t : Fin k × Fin k × Z' =>
      if t.1 = t.2.1 ∧ (Q.map fun t => (t.2.1, t.2.2)) (t.1, t.2.2) ≤
        L * (Q.map fun t => t.2.2) t.2.2 then 1 else 0) ?_
    refine iInf_le_of_le (fun t => by dsimp only; split_ifs <;> simp) ?_
    refine iInf_le_of_le (P_bound P Q ε δ η hε hδ hη0 hP_err hP_sec) ?_
    exact Q_bound Q hQ L
  -- `−log₂` is antitone
  have hlog2 : (0 : EReal) ≤ (((Real.log 2)⁻¹ : ℝ) : EReal) := by
    exact_mod_cast (inv_nonneg.mpr (Real.log_nonneg (by norm_num)))
  have h1 : WiretapFeedback.negLog2 L ≤
      WiretapFeedback.negLog2 (WiretapFeedback.testBeta (ε + δ + η) P Q) := by
    unfold WiretapFeedback.negLog2
    exact mul_le_mul_of_nonneg_right (EReal.neg_le_neg_iff.mpr (ENNReal.log_le_log hβ)) hlog2
  have h2 : WiretapFeedback.negLog2 L = ((Real.logb 2 (k * η) : ℝ) : EReal) := by
    unfold WiretapFeedback.negLog2
    rw [hL, ENNReal.log_ofReal_of_pos (by positivity), ← EReal.coe_neg, ← EReal.coe_mul]
    congr 1
    rw [Real.logb, one_div, Real.log_inv]
    ring
  have hreal : Real.logb 2 k ≤ Real.logb 2 (k * η) + 2 * Real.logb 2 (1 / η) := by
    have hη1' : η ≤ 1 := by linarith
    rw [Real.logb_mul (by exact_mod_cast hk.ne') hη0.ne', one_div, Real.logb_inv]
    have : Real.logb 2 η ≤ 0 := Real.logb_nonpos (by norm_num) hη0.le hη1'
    linarith
  calc ((Real.logb 2 k : ℝ) : EReal)
      ≤ ((Real.logb 2 (k * η) : ℝ) : EReal) + ((2 * Real.logb 2 (1 / η) : ℝ) : EReal) := by
        rw [← EReal.coe_add]; exact_mod_cast hreal
    _ = WiretapFeedback.negLog2 L + ((2 * Real.logb 2 (1 / η) : ℝ) : EReal) := by rw [h2]
    _ ≤ _ := add_le_add h1 le_rfl

namespace CodeLawAux

open WiretapFeedback

lemma map_const' {α β : Type} (p : PMF α) (f : α → β) (b : β) (hf : ∀ a, f a = b) :
    p.map f = PMF.pure b := by
  have : f = Function.const α b := funext hf
  rw [this, PMF.map_const]

lemma runLaw_map_fst {X O : Type} [Fintype O] {n : ℕ} (S : FeedbackStrategy X O n)
    (W : WildeQIT.Channel X O) : (S.runLaw W).map (fun r => r.1) = S.lawX := by
  unfold FeedbackStrategy.runLaw
  rw [PMF.map_bind]
  conv_rhs => rw [← PMF.bind_pure S.lawX]
  congr 1
  funext ux
  rw [PMF.map_bind]
  have : ∀ uy, ((FeedbackStrategy.runLaw.go S W ux uy n le_rfl).map fun o => (ux, uy, o)).map
      (fun r => r.1) = PMF.pure ux := fun uy => by
    rw [PMF.map_comp]; exact map_const' _ _ _ (fun o => rfl)
  simp only [this, PMF.bind_const]

/-- Under the code law, the message is distributed as `μ`. -/
lemma law_map_fst {X Y Z : Type} [Fintype Y] [Fintype Z] {N n : ℕ}
    (c : WiretapCode X Y N n) (μ : PMF (Fin N)) (W : WildeQIT.Channel X (Y × Z)) :
    (c.law μ W).map Prod.fst = μ := by
  unfold WiretapCode.law
  rw [PMF.map_comp]
  show PMF.map ((fun ux : (c.toStrategy Z μ).Ux => (ux : Fin N × c.Ux).1) ∘ (fun r => r.1))
    ((c.toStrategy Z μ).runLaw W) = μ
  rw [← PMF.map_comp, runLaw_map_fst]
  show (μ.bind fun m => c.lawX.map fun u => (m, u)).map (fun ux => ux.1) = μ
  rw [PMF.map_bind]
  conv_rhs => rw [← PMF.bind_pure μ]
  congr 1
  funext m
  rw [PMF.map_comp]
  exact map_const' _ _ _ (fun u => rfl)

end CodeLawAux


open CodeLawAux in
theorem solution {X Y Z : Type} [Fintype Y] [Fintype Z] {N n : ℕ} [NeZero N]
    (W V : WildeQIT.Channel X (Y × Z)) (V₂ : WildeQIT.Channel X Z) (V₁ : WildeQIT.Channel Z Y)
    (hV : ∀ x y z, (V x).prob (y, z) = (V₂ x).prob z * (V₁ z).prob y)
    (ε δ η : ℝ) (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (hεδ : ε + δ < 1)
    (c : WiretapFeedback.WiretapCode X Y N n) (hc : WiretapFeedback.IsWiretapCode W c ε δ)
    (hη0 : 0 < η) (hη1 : η < 1 - ε - δ) :
    ((Real.logb 2 N : ℝ) : EReal) ≤
      WiretapFeedback.negLog2 (WiretapFeedback.testBeta (ε + δ + η)
          (c.law (PMF.uniformOfFintype (Fin N)) W)
          (c.law (PMF.uniformOfFintype (Fin N)) V)) +
        ((2 * Real.logb 2 (1 / η) : ℝ) : EReal) := by
  obtain ⟨herr, hsec⟩ := hc
  rw [law_map_fst] at hsec
  refine sk_bound N ε δ η hε hδ hεδ _ _ herr hsec ?_ hη0 hη1
  intro a b zf
  exact WiretapFeedback.condIndep_message_decoded V V₂ V₁ hV c _ a b zf.1 zf.2
