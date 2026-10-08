-- Prove2me | solution 1 for SolomonRWRE.Recurrence.proof_1_7_boundary
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T20:14:05.145266+00:00
-- url     : https://prove2.me/submissions/f60b44ba-a459-4ec9-b5a0-0fe9c6e0795d

import Mathlib
import Definitions.Def_SolomonRWRE_Recurrence_Model

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal


namespace SolomonRWRE.Recurrence

/-- quenched cylinder weight -/
noncomputable def cylW (n : ℕ) (x : ℕ → ℤ) (a : ℤ → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((if x 0 = 0 then 1 else 0) * ∏ k ∈ Finset.range n, step a (x k) (x (k + 1)))

def cyl (n : ℕ) (x : ℕ → ℤ) : Set (ℕ → ℤ) := {w | ∀ k ≤ n, w k = x k}

lemma measurable_step (x y : ℤ) : Measurable fun a : ℤ → ℝ => step a x y := by
  unfold step
  split_ifs
  · exact measurable_pi_apply x
  · exact measurable_const.sub (measurable_pi_apply x)
  · exact measurable_const

lemma measurable_cylW (n : ℕ) (x : ℕ → ℤ) : Measurable (cylW n x) := by
  unfold cylW
  refine Measurable.ennreal_ofReal ?_
  refine Measurable.const_mul ?_ _
  exact Finset.measurable_prod _ fun k _ => measurable_step _ _

lemma measurableSet_cyl (n : ℕ) (x : ℕ → ℤ) : MeasurableSet (cyl n x) := by
  have : cyl n x = ⋂ k, ⋂ (_ : k ≤ n), (fun w : ℕ → ℤ => w k) ⁻¹' {x k} := by
    ext w; simp [cyl]
  rw [this]
  exact MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ =>
    measurable_pi_apply k (measurableSet_singleton _)

def extP (p : Σ n : ℕ, Fin (n + 1) → ℤ) : ℕ → ℤ :=
  fun k => if h : k < p.1 + 1 then p.2 ⟨k, h⟩ else 0

lemma extP_eq (n : ℕ) (w : ℕ → ℤ) : ∀ k ≤ n, extP ⟨n, fun i => w i⟩ k = w k := by
  intro k hk; simp only [extP, dif_pos (Nat.lt_succ_of_le hk)]

lemma cylW_congr {n : ℕ} {w w' : ℕ → ℤ} (a : ℤ → ℝ) (h : ∀ k ≤ n, w k = w' k) :
    cylW n w a = cylW n w' a := by
  unfold cylW
  rw [h 0 (Nat.zero_le _)]
  congr 2
  refine Finset.prod_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  rw [h k (by omega), h (k + 1) (by omega)]

lemma cyl_extP (n : ℕ) (x : ℕ → ℤ) :
    cyl n (extP ⟨n, fun i => x i⟩) = cyl n x := by
  ext w
  simp only [cyl, Set.mem_setOf_eq]
  constructor
  · intro h k hk; rw [h k hk, extP_eq n x k hk]
  · intro h k hk; rw [h k hk, extP_eq n x k hk]

lemma cylW_extP (n : ℕ) (x : ℕ → ℤ) (a : ℤ → ℝ) :
    cylW n (extP ⟨n, fun i => x i⟩) a = cylW n x a :=
  cylW_congr a (extP_eq n x)

theorem theorem_0_1_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (α : ℤ → Ω → ℝ) (X : ℕ → Ω → ℤ) (hRW : IsRWRE P α X)
    (S : Set (ℕ → ℤ)) (hS : MeasurableSet S)
    (h : ∀ᵐ a ∂(P.map (env α)), ∀ ν : Measure (ℕ → ℤ), IsProbabilityMeasure ν →
      IsChainInEnv ν a 0 (fun n w => w n) → ν S = 1) :
    P {ω | (fun n => X n ω) ∈ S} = 1 := by
  have hZ : Measurable (env α) := measurable_pi_iff.mpr fun n => hRW.meas_α n
  have hY : Measurable (fun ω n => X n ω) := measurable_pi_iff.mpr fun n => hRW.meas_X n
  haveI : IsProbabilityMeasure (P.map (env α)) := Measure.isProbabilityMeasure_map hZ.aemeasurable
  -- key identity
  have key : ∀ (n : ℕ) (x : ℕ → ℤ), ∀ᵐ a ∂(P.map (env α)),
      condDistrib (fun ω n => X n ω) (env α) P a (cyl n x) = cylW n x a := by
    intro n x
    refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite
      (Kernel.measurable_coe _ (measurableSet_cyl n x)) (measurable_cylW n x) ?_
    intro t ht _
    rw [setLIntegral_map ht (Kernel.measurable_coe _ (measurableSet_cyl n x)) hZ,
      setLIntegral_map ht (measurable_cylW n x) hZ,
      setLIntegral_preimage_condDistrib hZ hY.aemeasurable (measurableSet_cyl n x) ht]
    exact hRW.law n x t ht
  have key2 : ∀ᵐ a ∂(P.map (env α)), ∀ p : Σ n : ℕ, Fin (n+1) → ℤ,
      condDistrib (fun ω n => X n ω) (env α) P a (cyl p.1 (extP p)) = cylW p.1 (extP p) a :=
    ae_all_iff.mpr fun p => key p.1 (extP p)
  have hmem : ∀ᵐ a ∂(P.map (env α)), ∀ j, a j ∈ Set.Icc (0:ℝ) 1 := by
    have hms : MeasurableSet {a : ℤ → ℝ | ∀ j, a j ∈ Set.Icc (0:ℝ) 1} := by
      have : {a : ℤ → ℝ | ∀ j, a j ∈ Set.Icc (0:ℝ) 1} =
          ⋂ j, (fun a : ℤ → ℝ => a j) ⁻¹' Set.Icc 0 1 := by ext; simp
      rw [this]
      exact MeasurableSet.iInter fun j => measurable_pi_apply j measurableSet_Icc
    rw [ae_map_iff hZ.aemeasurable hms]
    exact Filter.Eventually.of_forall fun ω j => hRW.mem j ω
  have hfin : ∀ᵐ a ∂(P.map (env α)), condDistrib (fun ω n => X n ω) (env α) P a S = 1 := by
    filter_upwards [h, key2, hmem] with a ha hk hm
    refine ha _ inferInstance ⟨hm, fun n => measurable_pi_apply n, ?_⟩
    intro n x
    have := hk ⟨n, fun i => x i⟩
    rw [cyl_extP, cylW_extP] at this
    exact this
  have h1 : P {ω | (fun n => X n ω) ∈ S} =
      ∫⁻ a, condDistrib (fun ω n => X n ω) (env α) P a S ∂(P.map (env α)) := by
    have := setLIntegral_preimage_condDistrib (μ := P) hZ hY.aemeasurable hS MeasurableSet.univ
    rw [Set.preimage_univ, Set.univ_inter, Measure.restrict_univ] at this
    rw [lintegral_map (Kernel.measurable_coe _ hS) hZ, this]
    rfl
  rw [h1, lintegral_congr_ae hfin, lintegral_one, measure_univ]

/-! ## Quenched analysis for environments with reflecting sites -/

section Quenched
variable {ν : Measure (ℕ → ℤ)} {a : ℤ → ℝ}

lemma chain_cyl (hν : IsChainInEnv ν a 0 (fun n w => w n)) (n : ℕ) (x : ℕ → ℤ) :
    ν (cyl n x) = cylW n x a := hν.2.2 n x

lemma null_cylW_zero (hν : IsChainInEnv ν a 0 (fun n w => w n)) (n : ℕ) :
    ν {w | cylW n w a = 0} = 0 := by
  have hsub : {w | cylW n w a = 0} ⊆
      ⋃ v : Fin (n + 1) → ℤ, ⋃ (_ : cylW n (extP ⟨n, v⟩) a = 0), cyl n (extP ⟨n, v⟩) := by
    intro w hw
    simp only [Set.mem_setOf_eq] at hw
    refine Set.mem_iUnion.mpr ⟨fun i => w i, Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩
    · rw [cylW_congr a (extP_eq n w)]; exact hw
    · intro k hk; exact (extP_eq n w k hk).symm
  refine measure_mono_null hsub (measure_iUnion_null fun v => measure_iUnion_null fun hv => ?_)
  rw [chain_cyl hν]; exact hv

/-- paths with positive cylinder weights -/
def Good (a : ℤ → ℝ) : Set (ℕ → ℤ) := {w | w 0 = 0 ∧ ∀ k, step a (w k) (w (k + 1)) ≠ 0}

lemma null_good_compl (hν : IsChainInEnv ν a 0 (fun n w => w n)) : ν (Good a)ᶜ = 0 := by
  have hsub : (Good a)ᶜ ⊆ ⋃ n, {w | cylW n w a = 0} := by
    intro w hw
    simp only [Good, Set.mem_compl_iff, Set.mem_setOf_eq, not_and, not_forall, not_not] at hw
    by_cases h0 : w 0 = 0
    · obtain ⟨k, hk⟩ := hw h0
      refine Set.mem_iUnion.mpr ⟨k + 1, ?_⟩
      simp only [Set.mem_setOf_eq, cylW]
      rw [Finset.prod_eq_zero (Finset.mem_range.mpr (Nat.lt_succ_self k)) hk]; simp
    · refine Set.mem_iUnion.mpr ⟨0, ?_⟩
      simp [cylW, h0]
  exact measure_mono_null hsub (measure_iUnion_null fun n => null_cylW_zero hν n)

lemma step_ne_zero_cases {z z' : ℤ} (h : step a z z' ≠ 0) : z' = z + 1 ∨ z' = z - 1 := by
  unfold step at h; split_ifs at h with h1 h2
  · exact Or.inl h1
  · exact Or.inr h2
  · exact absurd rfl h

lemma step_refl {z z' : ℤ} (h : step a z z' ≠ 0) (hz : a z = 1) : z' = z + 1 := by
  unfold step at h; split_ifs at h with h1 h2
  · exact h1
  · rw [hz] at h; simp at h
  · exact absurd rfl h

lemma step_nonneg (ha : ∀ t, a t ∈ Set.Icc (0:ℝ) 1) (z z' : ℤ) : 0 ≤ step a z z' := by
  unfold step; split_ifs
  · exact (ha z).1
  · linarith [(ha z).2]
  · exact le_rfl

lemma good_stay_ge {w : ℕ → ℤ} (hw : w ∈ Good a) {r : ℤ} (hr : a r = 1) {n : ℕ}
    (hn : r ≤ w n) : ∀ m, n ≤ m → r ≤ w m := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => exact hn
  | succ m _ ih =>
    rcases step_ne_zero_cases (hw.2 m) with h | h
    · rw [h]; omega
    · rcases eq_or_lt_of_le ih with h' | h'
      · have := step_refl (hw.2 m) (by rw [← h']; exact hr); omega
      · rw [h]; omega

lemma good_ge_left {w : ℕ → ℤ} (hw : w ∈ Good a) {l : ℤ} (hl : a l = 1) (hl0 : l ≤ 0) :
    ∀ m, l ≤ w m := fun m =>
  good_stay_ge hw hl (n := 0) (by rw [hw.1]; exact hl0) m (Nat.zero_le _)

lemma prod_lower (ha : ∀ t, a t ∈ Set.Icc (0:ℝ) 1) (I : Finset ℤ) (z : ℤ) (j : ℕ)
    (hz : ∀ i < j, z + i ∈ I) :
    ∏ t ∈ I, a t ≤ ∏ i ∈ Finset.range j, a (z + i) := by
  classical
  have himg : ∏ i ∈ Finset.range j, a (z + i) =
      ∏ t ∈ (Finset.range j).image (fun i : ℕ => z + i), a t := by
    rw [Finset.prod_image]
    intro x _ y _ h
    exact_mod_cast add_left_cancel h
  rw [himg]
  have hsub : (Finset.range j).image (fun i : ℕ => z + i) ⊆ I := by
    intro t ht
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ht
    exact hz i (Finset.mem_range.mp hi)
  rw [← Finset.prod_sdiff hsub]
  refine mul_le_of_le_one_left (Finset.prod_nonneg fun t _ => (ha t).1) ?_
  exact Finset.prod_le_one (fun t _ => (ha t).1) (fun t _ => (ha t).2)

/-- the path that follows `x` up to time `N` and then steps right -/
def exitPath (N : ℕ) (x : ℕ → ℤ) : ℕ → ℤ :=
  fun k => if k < N then x k else x N + ((k - N : ℕ) : ℤ)

lemma exitPath_eq (N : ℕ) (x : ℕ → ℤ) : ∀ k ≤ N, exitPath N x k = x k := by
  intro k hk
  unfold exitPath
  split_ifs with h
  · rfl
  · have : k = N := by omega
    subst this; simp

lemma exitPath_add (N : ℕ) (x : ℕ → ℤ) (i : ℕ) : exitPath N x (N + i) = x N + i := by
  unfold exitPath
  rw [if_neg (by omega), Nat.add_sub_cancel_left]

lemma cylW_exit (ha : ∀ t, a t ∈ Set.Icc (0:ℝ) 1) (N j : ℕ) (x : ℕ → ℤ) :
    cylW (N + j) (exitPath N x) a =
      cylW N x a * ENNReal.ofReal (∏ i ∈ Finset.range j, a (x N + i)) := by
  unfold cylW
  rw [Finset.prod_range_add, ← ENNReal.ofReal_mul
    (mul_nonneg (by split_ifs <;> norm_num) (Finset.prod_nonneg fun k _ => step_nonneg ha _ _)),
    mul_assoc, exitPath_eq N x 0 (Nat.zero_le _)]
  congr 3
  · refine Finset.prod_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hk
    rw [exitPath_eq N x k (by omega), exitPath_eq N x (k + 1) (by omega)]
  · refine Finset.prod_congr rfl fun i _ => ?_
    rw [exitPath_add, show N + i + 1 = N + (i + 1) by ring, exitPath_add]
    unfold step
    rw [if_pos (by push_cast; ring)]

lemma cyl_exit_subset (N j : ℕ) (x : ℕ → ℤ) : cyl (N + j) (exitPath N x) ⊆ cyl N x := by
  intro w hw k hk
  rw [hw k (by omega), exitPath_eq N x k hk]

lemma stay_step (hν : IsChainInEnv ν a 0 (fun n w => w n)) [IsProbabilityMeasure ν]
    (l r : ℤ) (N : ℕ) :
    ν {w | ∀ k ≤ N + (r - l).toNat, w k ∈ Set.Icc l (r - 1)} ≤
      (1 - ENNReal.ofReal (∏ t ∈ Finset.Icc l (r - 1), a t)) *
        ν {w | ∀ k ≤ N, w k ∈ Set.Icc l (r - 1)} := by
  classical
  have ha := hν.1
  set m := (r - l).toNat with hm
  set ε := ∏ t ∈ Finset.Icc l (r - 1), a t with hε
  set F : Finset (Fin (N + 1) → ℤ) := Fintype.piFinset fun _ => Finset.Icc l (r - 1) with hF
  let X : (Fin (N + 1) → ℤ) → ℕ → ℤ := fun v => extP ⟨N, v⟩
  let J : (Fin (N + 1) → ℤ) → ℕ := fun v => (r - v (Fin.last N)).toNat
  have hXN : ∀ v, X v N = v (Fin.last N) := fun v => by
    simp only [X, extP, dif_pos (Nat.lt_succ_self N)]; rfl
  have hXk : ∀ v (k : ℕ) (hk : k < N + 1), X v k = v ⟨k, hk⟩ := fun v k hk => by
    simp only [X, extP, dif_pos hk]
  have hsub : {w | ∀ k ≤ N + m, w k ∈ Set.Icc l (r - 1)} ⊆
      ⋃ v ∈ F, (cyl N (X v) \ cyl (N + J v) (exitPath N (X v))) := by
    intro w hw
    simp only [Set.mem_setOf_eq] at hw
    have hv : (fun i : Fin (N + 1) => w i) ∈ F := by
      simp only [hF, Fintype.mem_piFinset]
      intro i; exact Finset.mem_Icc.mpr (hw i (by omega))
    refine Set.mem_biUnion hv ⟨?_, ?_⟩
    · intro k hk; exact (extP_eq N w k hk).symm
    · intro hex
      have hwN := hw N (by omega)
      rw [Set.mem_Icc] at hwN
      have hJ : (J (fun i : Fin (N + 1) => w i) : ℤ) = r - w N := by
        simp only [J, Fin.val_last]
        exact Int.toNat_of_nonneg (by omega)
      have hJm : J (fun i : Fin (N + 1) => w i) ≤ m := by
        simp only [J, Fin.val_last, hm]
        exact Int.toNat_le_toNat (by omega)
      have h1 := hex (N + J (fun i : Fin (N + 1) => w i)) le_rfl
      rw [exitPath_add, hXN] at h1
      simp only [Fin.val_last] at h1
      have h2 := hw (N + J (fun i : Fin (N + 1) => w i)) (by omega)
      rw [Set.mem_Icc] at h2
      omega
  have hsum : ∑ v ∈ F, ν (cyl N (X v)) = ν {w | ∀ k ≤ N, w k ∈ Set.Icc l (r - 1)} := by
    rw [← measure_biUnion_finset]
    · congr 1; ext w
      simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
      constructor
      · rintro ⟨v, hv, hw⟩ k hk
        rw [hw k hk, hXk v k (Nat.lt_succ_of_le hk)]
        exact Finset.mem_Icc.mp ((Fintype.mem_piFinset.mp hv) _)
      · intro hw
        refine ⟨fun i => w i, ?_, fun k hk => (extP_eq N w k hk).symm⟩
        simp only [hF, Fintype.mem_piFinset]
        intro i; exact Finset.mem_Icc.mpr (hw i (by omega))
    · intro v _ v' _ hne
      rw [Function.onFun, Set.disjoint_left]
      intro w hw hw'
      apply hne; funext i
      have h1 := hw i (by omega); have h2 := hw' i (by omega)
      rw [hXk v i i.isLt] at h1; rw [hXk v' i i.isLt] at h2
      rw [← h1, ← h2]
    · exact fun v _ => measurableSet_cyl _ _
  have hterm : ∀ v ∈ F, ν (cyl N (X v) \ cyl (N + J v) (exitPath N (X v))) ≤
      (1 - ENNReal.ofReal ε) * ν (cyl N (X v)) := by
    intro v hv
    have hvI : v (Fin.last N) ∈ Finset.Icc l (r - 1) := (Fintype.mem_piFinset.mp hv) _
    rw [Finset.mem_Icc] at hvI
    have hlow : ν (cyl N (X v)) * ENNReal.ofReal ε ≤ ν (cyl N (X v) ∩ cyl (N + J v) (exitPath N (X v))) := by
      rw [Set.inter_eq_right.mpr (cyl_exit_subset _ _ _), chain_cyl hν, chain_cyl hν, cylW_exit ha]
      refine mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal ?_)
      refine prod_lower ha _ _ _ fun i hi => ?_
      rw [hXN, Finset.mem_Icc]
      have : (i : ℤ) < r - v (Fin.last N) := by
        have := (Int.lt_toNat.mp hi)
        exact this
      constructor <;> omega
    rw [measure_diff (cyl_exit_subset _ _ _) (measurableSet_cyl _ _).nullMeasurableSet
      (measure_ne_top _ _), Set.inter_eq_right.mpr (cyl_exit_subset _ _ _)] at *
    calc ν (cyl N (X v)) - ν (cyl (N + J v) (exitPath N (X v)))
        ≤ ν (cyl N (X v)) - ν (cyl N (X v)) * ENNReal.ofReal ε := tsub_le_tsub_left hlow _
      _ = (1 - ENNReal.ofReal ε) * ν (cyl N (X v)) := by
        rw [ENNReal.sub_mul (fun _ _ => measure_ne_top _ _), one_mul, mul_comm]
  calc ν {w | ∀ k ≤ N + m, w k ∈ Set.Icc l (r - 1)}
      ≤ ν (⋃ v ∈ F, (cyl N (X v) \ cyl (N + J v) (exitPath N (X v)))) := measure_mono hsub
    _ ≤ ∑ v ∈ F, ν (cyl N (X v) \ cyl (N + J v) (exitPath N (X v))) :=
        measure_biUnion_finset_le F _
    _ ≤ ∑ v ∈ F, (1 - ENNReal.ofReal ε) * ν (cyl N (X v)) := Finset.sum_le_sum hterm
    _ = (1 - ENNReal.ofReal ε) * ∑ v ∈ F, ν (cyl N (X v)) := by rw [Finset.mul_sum]
    _ = _ := by rw [hsum]

lemma stay_pow (hν : IsChainInEnv ν a 0 (fun n w => w n)) [IsProbabilityMeasure ν]
    (l r : ℤ) (N : ℕ) :
    ν {w | ∀ k ≤ N * (r - l).toNat, w k ∈ Set.Icc l (r - 1)} ≤
      (1 - ENNReal.ofReal (∏ t ∈ Finset.Icc l (r - 1), a t)) ^ N := by
  induction N with
  | zero => simp only [zero_mul, pow_zero]; exact prob_le_one
  | succ N ih =>
    calc ν {w | ∀ k ≤ (N + 1) * (r - l).toNat, w k ∈ Set.Icc l (r - 1)}
        = ν {w | ∀ k ≤ N * (r - l).toNat + (r - l).toNat, w k ∈ Set.Icc l (r - 1)} := by
          rw [Nat.succ_mul]
      _ ≤ (1 - ENNReal.ofReal (∏ t ∈ Finset.Icc l (r - 1), a t)) *
          ν {w | ∀ k ≤ N * (r - l).toNat, w k ∈ Set.Icc l (r - 1)} := stay_step hν l r _
      _ ≤ (1 - ENNReal.ofReal (∏ t ∈ Finset.Icc l (r - 1), a t)) *
          (1 - ENNReal.ofReal (∏ t ∈ Finset.Icc l (r - 1), a t)) ^ N := mul_le_mul' le_rfl ih
      _ = _ := (pow_succ' _ _).symm

lemma ennreal_pow_tendsto_zero {q : ℝ≥0∞} (hq : q < 1) :
    Tendsto (fun N : ℕ => q ^ N) atTop (𝓝 0) := by
  have hqt : q = ENNReal.ofReal q.toReal := (ENNReal.ofReal_toReal hq.ne_top).symm
  have h1 : q.toReal < 1 := by
    have := (ENNReal.toReal_lt_toReal hq.ne_top ENNReal.one_ne_top).mpr hq
    simpa using this
  have h2 := ENNReal.tendsto_ofReal
    (tendsto_pow_atTop_nhds_zero_of_lt_one ENNReal.toReal_nonneg h1)
  rw [ENNReal.ofReal_zero] at h2
  refine h2.congr fun N => ?_
  rw [ENNReal.ofReal_pow ENNReal.toReal_nonneg, ← hqt]

lemma stay_null (hν : IsChainInEnv ν a 0 (fun n w => w n)) [IsProbabilityMeasure ν]
    (hpos : ∀ t, 0 < a t) (l r : ℤ) :
    ν {w | ∀ k, w k ∈ Set.Icc l (r - 1)} = 0 := by
  have ha := hν.1
  set ε := ∏ t ∈ Finset.Icc l (r - 1), a t with hε
  have hε0 : 0 < ε := Finset.prod_pos fun t _ => hpos t
  have hq : 1 - ENNReal.ofReal ε < 1 :=
    ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero (ENNReal.ofReal_pos.mpr hε0).ne'
  have hlim := ennreal_pow_tendsto_zero hq
  refine le_antisymm (ge_of_tendsto' hlim fun N => ?_) zero_le
  refine le_trans (measure_mono ?_) (stay_pow hν l r N)
  intro w hw k _
  exact hw k

lemma measurableSet_tendsto_atTop : MeasurableSet {w : ℕ → ℤ | Tendsto w atTop atTop} := by
  have : {w : ℕ → ℤ | Tendsto w atTop atTop} = ⋂ M : ℤ, ⋃ n : ℕ, ⋂ m : ℕ, ⋂ (_ : n ≤ m),
      (fun w : ℕ → ℤ => w m) ⁻¹' Set.Ici M := by
    ext w; simp [tendsto_atTop_atTop]
  rw [this]
  exact MeasurableSet.iInter fun M => MeasurableSet.iUnion fun n => MeasurableSet.iInter fun m =>
    MeasurableSet.iInter fun _ => measurable_pi_apply m measurableSet_Ici

lemma quenched_tendsto (hν : IsChainInEnv ν a 0 (fun n w => w n)) [IsProbabilityMeasure ν]
    (hpos : ∀ t, 0 < a t) (hR : ∀ M : ℤ, ∃ r, M ≤ r ∧ a r = 1) (hL : ∃ l, l ≤ 0 ∧ a l = 1) :
    ν {w | Tendsto w atTop atTop} = 1 := by
  obtain ⟨l, hl0, hl⟩ := hL
  have hG : ∀ᵐ w ∂ν, w ∈ Good a := by
    rw [ae_iff]; exact null_good_compl hν
  have hM : ∀ M : ℤ, ∀ᵐ w ∂ν, w ∈ Good a → ∃ n, ∀ m, n ≤ m → M ≤ w m := by
    intro M
    obtain ⟨r, hMr, hr⟩ := hR (max M 0)
    have h0 := stay_null hν hpos l r
    rw [ae_iff]
    refine measure_mono_null ?_ h0
    intro w hw
    simp only [Set.mem_setOf_eq, Classical.not_imp, not_exists, not_forall, not_le] at hw
    obtain ⟨hwG, hw⟩ := hw
    intro k
    rw [Set.mem_Icc]
    refine ⟨good_ge_left hwG hl hl0 k, ?_⟩
    by_contra hcon
    push_neg at hcon
    obtain ⟨m, hm, hlt⟩ := hw k
    have := good_stay_ge hwG hr (n := k) (by omega) m hm
    omega
  have hae : ∀ᵐ w ∂ν, Tendsto w atTop atTop := by
    filter_upwards [hG, ae_all_iff.mpr hM] with w hw hM'
    rw [tendsto_atTop_atTop]
    intro M
    exact hM' M hw
  have := ae_iff.mp hae
  rwa [← Set.compl_setOf, prob_compl_eq_zero_iff measurableSet_tendsto_atTop] at this

end Quenched

/-! ## Annealed part -/

section Annealed
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {α : ℤ → Ω → ℝ} {X : ℕ → Ω → ℤ}

lemma prob_none_eq (hRW : IsRWRE P α X) (c : ℝ) (F : Finset ℤ) :
    P {ω | ∀ k ∈ F, α k ω ≠ c} = (P {ω | α 0 ω ≠ c}) ^ F.card := by
  have h := (iIndepFun_iff_measure_inter_preimage_eq_mul.mp hRW.indep) F
    (sets := fun _ => {c}ᶜ) (fun i _ => (measurableSet_singleton c).compl)
  have hset : {ω | ∀ k ∈ F, α k ω ≠ c} = ⋂ i ∈ F, α i ⁻¹' {c}ᶜ := by ext; simp
  rw [hset, h, Finset.prod_congr rfl
    (fun i _ => (hRW.ident i).measure_mem_eq (measurableSet_singleton c).compl), Finset.prod_const]
  rfl

lemma q_lt_one (hRW : IsRWRE P α X) {c : ℝ} (hp : 0 < P {ω | α 0 ω = c}) :
    P {ω | α 0 ω ≠ c} < 1 := by
  have hm : MeasurableSet {ω | α 0 ω = c} := hRW.meas_α 0 (measurableSet_singleton c)
  have : {ω | α 0 ω ≠ c} = {ω | α 0 ω = c}ᶜ := rfl
  rw [this, prob_compl_eq_one_sub hm]
  exact ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hp.ne'

lemma ae_exists_right (hRW : IsRWRE P α X) {c : ℝ} (hp : 0 < P {ω | α 0 ω = c}) (M : ℤ) :
    ∀ᵐ ω ∂P, ∃ r, M ≤ r ∧ α r ω = c := by
  rw [ae_iff]
  have hq := q_lt_one hRW hp
  have hbound : ∀ N : ℕ, P {ω | ¬ ∃ r, M ≤ r ∧ α r ω = c} ≤ (P {ω | α 0 ω ≠ c}) ^ (N + 1) := by
    intro N
    have hsub : {ω | ¬ ∃ r, M ≤ r ∧ α r ω = c} ⊆
        {ω | ∀ k ∈ Finset.Icc M (M + N), α k ω ≠ c} := by
      intro ω hω
      simp only [Set.mem_setOf_eq, not_exists, not_and] at hω ⊢
      intro k hk; exact hω k (Finset.mem_Icc.mp hk).1
    calc P _ ≤ P {ω | ∀ k ∈ Finset.Icc M (M + N), α k ω ≠ c} := measure_mono hsub
      _ = (P {ω | α 0 ω ≠ c}) ^ (Finset.Icc M (M + N)).card := prob_none_eq hRW c _
      _ = (P {ω | α 0 ω ≠ c}) ^ (N + 1) := by
          congr 1; rw [Int.card_Icc]; omega
  have hlim : Tendsto (fun N : ℕ => (P {ω | α 0 ω ≠ c}) ^ (N + 1)) atTop (𝓝 0) :=
    (ennreal_pow_tendsto_zero hq).comp (tendsto_add_atTop_nat 1)
  exact le_antisymm (ge_of_tendsto' hlim hbound) zero_le

lemma ae_exists_left (hRW : IsRWRE P α X) {c : ℝ} (hp : 0 < P {ω | α 0 ω = c}) (M : ℤ) :
    ∀ᵐ ω ∂P, ∃ l, l ≤ M ∧ α l ω = c := by
  rw [ae_iff]
  have hq := q_lt_one hRW hp
  have hbound : ∀ N : ℕ, P {ω | ¬ ∃ l, l ≤ M ∧ α l ω = c} ≤ (P {ω | α 0 ω ≠ c}) ^ (N + 1) := by
    intro N
    have hsub : {ω | ¬ ∃ l, l ≤ M ∧ α l ω = c} ⊆
        {ω | ∀ k ∈ Finset.Icc (M - N) M, α k ω ≠ c} := by
      intro ω hω
      simp only [Set.mem_setOf_eq, not_exists, not_and] at hω ⊢
      intro k hk; exact hω k (Finset.mem_Icc.mp hk).2
    calc P _ ≤ P {ω | ∀ k ∈ Finset.Icc (M - N) M, α k ω ≠ c} := measure_mono hsub
      _ = (P {ω | α 0 ω ≠ c}) ^ (Finset.Icc (M - N) M).card := prob_none_eq hRW c _
      _ = (P {ω | α 0 ω ≠ c}) ^ (N + 1) := by
          congr 1; rw [Int.card_Icc]; omega
  have hlim : Tendsto (fun N : ℕ => (P {ω | α 0 ω ≠ c}) ^ (N + 1)) atTop (𝓝 0) :=
    (ennreal_pow_tendsto_zero hq).comp (tendsto_add_atTop_nat 1)
  exact le_antisymm (ge_of_tendsto' hlim hbound) zero_le

lemma tsum_geom_bound (hRW : IsRWRE P α X) {c : ℝ} (hp : 0 < P {ω | α 0 ω = c})
    (f : ℕ → ℝ≥0∞) (hf : ∀ n, f n ≤ (P {ω | α 0 ω ≠ c}) ^ (n + 1)) :
    ∑' n, f n ≠ ∞ := by
  have hq := q_lt_one hRW hp
  refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hf)
  simp_rw [pow_succ']
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
  exact ENNReal.mul_ne_top hq.ne_top (ENNReal.inv_ne_top.mpr (tsub_pos_iff_lt.mpr hq).ne')

lemma seriesGt_ne_top (hRW : IsRWRE P α X) (hp : 0 < P {ω | α 0 ω = 1}) :
    seriesGt P α ≠ ∞ := by
  refine tsum_geom_bound hRW hp _ fun n => ?_
  calc ((n : ℝ≥0∞) + 1)⁻¹ * P {ω | 1 < rho (env α ω) ((n : ℤ) + 1)}
      ≤ 1 * P {ω | 1 < rho (env α ω) ((n : ℤ) + 1)} :=
        mul_le_mul' (ENNReal.inv_le_one.mpr le_add_self) le_rfl
    _ ≤ P {ω | ∀ k ∈ Finset.Icc (1 : ℤ) ((n : ℤ) + 1), α k ω ≠ 1} := by
        rw [one_mul]
        refine measure_mono fun ω hω => ?_
        simp only [Set.mem_setOf_eq] at hω ⊢
        intro k hk hk1
        have h0 : rho (env α ω) ((n : ℤ) + 1) = 0 := by
          unfold rho
          rw [if_pos (by omega)]
          refine Finset.prod_eq_zero hk ?_
          simp [sigma, env, hk1]
        rw [h0] at hω
        exact absurd hω (not_lt.mpr zero_le)
    _ = (P {ω | α 0 ω ≠ 1}) ^ (n + 1) := by
        rw [prob_none_eq hRW 1, Int.card_Icc]; congr 1; omega

lemma seriesLt_ne_top (hRW : IsRWRE P α X) (hp : 0 < P {ω | α 0 ω = 0})
    (hlt : ∀ n ω, α n ω < 1) : seriesLt P α ≠ ∞ := by
  refine tsum_geom_bound hRW hp _ fun n => ?_
  calc ((n : ℝ≥0∞) + 1)⁻¹ * P {ω | rho (env α ω) ((n : ℤ) + 1) < 1}
      ≤ 1 * P {ω | rho (env α ω) ((n : ℤ) + 1) < 1} :=
        mul_le_mul' (ENNReal.inv_le_one.mpr le_add_self) le_rfl
    _ ≤ P {ω | ∀ k ∈ Finset.Icc (1 : ℤ) ((n : ℤ) + 1), α k ω ≠ 0} := by
        rw [one_mul]
        refine measure_mono fun ω hω => ?_
        simp only [Set.mem_setOf_eq] at hω ⊢
        intro k hk hk0
        apply hω.ne_top
        unfold rho
        rw [if_pos (by omega), ← Finset.mul_prod_erase _ _ hk]
        have h1 : sigma (env α ω) k = ∞ := by
          simp [sigma, env, hk0]
        rw [h1]
        refine ENNReal.top_mul (Finset.prod_ne_zero_iff.mpr fun j _ => ?_)
        simp only [sigma, env, ne_eq, ENNReal.div_eq_zero_iff, ENNReal.ofReal_eq_zero, not_or,
          not_le, ENNReal.ofReal_ne_top]
        constructor
        · linarith [hlt j ω]
        · simp
    _ = (P {ω | α 0 ω ≠ 0}) ^ (n + 1) := by
        rw [prob_none_eq hRW 0, Int.card_Icc]; congr 1; omega

theorem boundary_right (hRW : IsRWRE P α X) (hp : 0 < P {ω | α 0 ω = 1})
    (hpos : ∀ n ω, 0 < α n ω) :
    seriesGt P α ≠ ∞ ∧ ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop atTop := by
  refine ⟨seriesGt_ne_top hRW hp, ?_⟩
  have hZ : Measurable (env α) := measurable_pi_iff.mpr fun n => hRW.meas_α n
  have hY : Measurable (fun ω n => X n ω) := measurable_pi_iff.mpr fun n => hRW.meas_X n
  have hA : ∀ᵐ a ∂(P.map (env α)), (∀ t, 0 < a t) ∧ (∀ M : ℤ, ∃ r, M ≤ r ∧ a r = 1) ∧
      (∃ l, l ≤ 0 ∧ a l = 1) := by
    have hms : MeasurableSet {a : ℤ → ℝ | (∀ t, 0 < a t) ∧ (∀ M : ℤ, ∃ r, M ≤ r ∧ a r = 1) ∧
        (∃ l, l ≤ 0 ∧ a l = 1)} := by
      have e : {a : ℤ → ℝ | (∀ t, 0 < a t) ∧ (∀ M : ℤ, ∃ r, M ≤ r ∧ a r = 1) ∧
          (∃ l, l ≤ 0 ∧ a l = 1)} =
          (⋂ t, (fun a : ℤ → ℝ => a t) ⁻¹' Set.Ioi 0) ∩
          ((⋂ M : ℤ, ⋃ r : ℤ, ⋃ (_ : M ≤ r), (fun a : ℤ → ℝ => a r) ⁻¹' {1}) ∩
            (⋃ l : ℤ, ⋃ (_ : l ≤ 0), (fun a : ℤ → ℝ => a l) ⁻¹' {1})) := by
        ext a; simp
      rw [e]
      refine (MeasurableSet.iInter fun t => measurable_pi_apply t measurableSet_Ioi).inter
        ((MeasurableSet.iInter fun M => MeasurableSet.iUnion fun r => MeasurableSet.iUnion fun _ =>
          measurable_pi_apply r (measurableSet_singleton 1)).inter
        (MeasurableSet.iUnion fun l => MeasurableSet.iUnion fun _ =>
          measurable_pi_apply l (measurableSet_singleton 1)))
    rw [ae_map_iff hZ.aemeasurable hms]
    have h1 := ae_all_iff.mpr (ae_exists_right hRW hp)
    have h2 := ae_exists_left hRW hp 0
    filter_upwards [h1, h2] with ω h1 h2
    exact ⟨fun t => hpos t ω, h1, h2⟩
  have hS : P {ω | (fun n => X n ω) ∈ {w | Tendsto w atTop atTop}} = 1 := by
    refine theorem_0_1_core P α X hRW _ measurableSet_tendsto_atTop ?_
    filter_upwards [hA] with a ha
    intro ν hν hchain
    exact quenched_tendsto hchain ha.1 ha.2.1 ha.2.2
  rw [ae_iff, ← Set.compl_setOf,
    prob_compl_eq_zero_iff (s := {ω | Tendsto (fun n => X n ω) atTop atTop})
      (hY measurableSet_tendsto_atTop)]
  exact hS

/-! ## Reflection -/

lemma step_reflect (a : ℤ → ℝ) (z z' : ℤ) :
    step (fun m => 1 - a (-m)) z z' = step a (-z) (-z') := by
  unfold step
  by_cases h1 : z' = z + 1
  · rw [if_pos h1, if_neg (by omega), if_pos (by omega)]
  · by_cases h2 : z' = z - 1
    · rw [if_neg h1, if_pos h2, if_pos (by omega)]; ring
    · rw [if_neg h1, if_neg h2, if_neg (by omega), if_neg (by omega)]

lemma isRWRE_reflect (hRW : IsRWRE P α X) :
    IsRWRE P (fun n ω => 1 - α (-n) ω) (fun n ω => -X n ω) where
  meas_α n := measurable_const.sub (hRW.meas_α (-n))
  meas_X n := (hRW.meas_X n).neg
  mem n ω := by
    have := hRW.mem (-n) ω
    rw [Set.mem_Icc] at this ⊢
    constructor <;> linarith
  indep := by
    have h := (hRW.indep.precomp (g := fun n : ℤ => -n) neg_injective).comp
      (fun _ t => 1 - t) (fun _ => measurable_const.sub measurable_id)
    exact h
  ident n := by
    have h := ((hRW.ident (-n)).trans (hRW.ident (-0)).symm).comp
      (u := fun t : ℝ => 1 - t) (measurable_const.sub measurable_id)
    exact h
  law := by
    intro n x A hA
    let R : (ℤ → ℝ) → (ℤ → ℝ) := fun a m => 1 - a (-m)
    have hRm : Measurable R :=
      measurable_pi_iff.mpr fun m => measurable_const.sub (measurable_pi_apply (-m))
    have e1 : {ω | (fun m => 1 - α (-m) ω) ∈ A} = {ω | (fun m => α m ω) ∈ R ⁻¹' A} := rfl
    have e2 : {ω | ∀ k ≤ n, -X k ω = x k} =
        {ω | ∀ k ≤ n, X k ω = (-x) k} := by
      ext ω; simp only [Set.mem_setOf_eq, Pi.neg_apply, neg_eq_iff_eq_neg]
    rw [e1, e2, hRW.law n (-x) (R ⁻¹' A) (hRm hA)]
    refine lintegral_congr fun ω => ?_
    simp only [Pi.neg_apply, neg_eq_zero]
    have hp : ∏ k ∈ Finset.range n, step (fun m => α m ω) (-x k) (-x (k + 1)) =
        ∏ k ∈ Finset.range n, step (fun m => 1 - α (-m) ω) (x k) (x (k + 1)) :=
      Finset.prod_congr rfl fun k _ => (step_reflect (fun m => α m ω) (x k) (x (k + 1))).symm
    rw [hp]

theorem boundary_left (hRW : IsRWRE P α X) (hp : 0 < P {ω | α 0 ω = 0})
    (hlt : ∀ n ω, α n ω < 1) :
    seriesLt P α ≠ ∞ ∧ ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop atBot := by
  refine ⟨seriesLt_ne_top hRW hp hlt, ?_⟩
  have hp' : 0 < P {ω | (fun n ω => 1 - α (-n) ω) 0 ω = 1} := by
    have : {ω | (fun n ω => 1 - α (-n) ω) 0 ω = 1} = {ω | α 0 ω = 0} := by
      ext ω; simp
    rw [this]; exact hp
  have h := (boundary_right (isRWRE_reflect hRW) hp' (fun n ω => sub_pos.mpr (hlt _ _))).2
  filter_upwards [h] with ω hω
  exact tendsto_neg_atTop_iff.mp hω

theorem proof_1_7_boundary_core (hRW : IsRWRE P α X) :
    ((0 < P {ω | α 0 ω = 1} ∧ ∀ n ω, 0 < α n ω) →
        seriesGt P α ≠ ∞ ∧ ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop atTop) ∧
    ((0 < P {ω | α 0 ω = 0} ∧ ∀ n ω, α n ω < 1) →
        seriesLt P α ≠ ∞ ∧ ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop atBot) :=
  ⟨fun h => boundary_right hRW h.1 h.2, fun h => boundary_left hRW h.1 h.2⟩

end Annealed

end SolomonRWRE.Recurrence

open SolomonRWRE.Recurrence


theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (α : ℤ → Ω → ℝ) (X : ℕ → Ω → ℤ) (hRW : IsRWRE P α X)
    (hnd : ¬ ∃ c : ℝ, ∀ᵐ ω ∂P, α 0 ω = c) :
    ((0 < P {ω | α 0 ω = 1} ∧ ∀ n ω, 0 < α n ω) →
        seriesGt P α ≠ ∞ ∧ ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop atTop) ∧
    ((0 < P {ω | α 0 ω = 0} ∧ ∀ n ω, α n ω < 1) →
        seriesLt P α ≠ ∞ ∧ ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop atBot) := by
  exact proof_1_7_boundary_core hRW
