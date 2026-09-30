-- Prove2me | solution 1 for SupplyChainTheory.long_chain_optimal
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-27T17:57:04.716505+00:00
-- url     : https://prove2.me/submissions/6c415f0f-4326-4bf1-a3cb-e6de99ecc27d

import Mathlib
import Definitions.Def_SupplyChainTheory_flexibility

set_option autoImplicit false

noncomputable def lci_step (C x a : ℝ) : ℝ := min C (max 0 (C + a - x))

noncomputable def lci_run (C : ℝ) (d : ℕ → ℝ) (a : ℝ) : ℕ → ℝ
  | 0 => a
  | j + 1 => lci_step C (d j) (lci_run C d a j)

noncomputable def lci_ext (n : ℕ) (x : Fin n → ℝ) (m : ℕ) : ℝ :=
  if h : m < n then x ⟨m, h⟩ else 0

noncomputable def lci_b (C : ℝ) (d : ℕ → ℝ) (k m : ℕ) : ℝ :=
  if m < k then lci_run C d 0 m else 0

noncomputable def lci_V (C : ℝ) (d : ℕ → ℝ) (k n : ℕ) : ℝ :=
  ∑ m ∈ Finset.range n, min (d m) (lci_b C d k m + C)

noncomputable def lci_f (C : ℝ) (d : ℕ → ℝ) (j : ℕ) : ℝ :=
  min (d j) (lci_run C d 0 j + C) - min (d j) C

lemma lci_step_mono (C x : ℝ) {a a' : ℝ} (h : a ≤ a') : lci_step C x a ≤ lci_step C x a' := by
  unfold lci_step
  exact min_le_min_left _ (max_le_max_left _ (by linarith))

lemma lci_step_nonneg {C : ℝ} (hC : 0 ≤ C) (x a : ℝ) : 0 ≤ lci_step C x a := by
  unfold lci_step
  exact le_min hC (le_max_left _ _)

lemma lci_run_mono (C : ℝ) (d : ℕ → ℝ) {a a' : ℝ} (h : a ≤ a') (j : ℕ) :
    lci_run C d a j ≤ lci_run C d a' j := by
  induction j with
  | zero => exact h
  | succ j ih => exact lci_step_mono C (d j) ih

lemma lci_run_nonneg {C : ℝ} (hC : 0 ≤ C) (d : ℕ → ℝ) {a : ℝ} (ha : 0 ≤ a) (j : ℕ) :
    0 ≤ lci_run C d a j := by
  cases j with
  | zero => exact ha
  | succ j => exact lci_step_nonneg hC _ _

lemma lci_run_shift (C : ℝ) (d : ℕ → ℝ) (a : ℝ) (j : ℕ) :
    lci_run C d a (j + 1) = lci_run C (fun m => d (m + 1)) (lci_step C (d 0) a) j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    show lci_step C (d (j + 1)) (lci_run C d a (j + 1))
      = lci_step C (d (j + 1)) (lci_run C (fun m => d (m + 1)) (lci_step C (d 0) a) j)
    rw [ih]

lemma lci_run_congr (C : ℝ) (d d' : ℕ → ℝ) (a : ℝ) (j : ℕ) (h : ∀ m < j, d m = d' m) :
    lci_run C d a j = lci_run C d' a j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    show lci_step C (d j) (lci_run C d a j) = lci_step C (d' j) (lci_run C d' a j)
    rw [ih (fun m hm => h m (by omega)), h j (by omega)]

lemma lci_run_tail_le (C : ℝ) (hC : 0 ≤ C) (d : ℕ → ℝ) (j : ℕ) :
    lci_run C (fun m => d (m + 1)) 0 j ≤ lci_run C d 0 (j + 1) := by
  rw [lci_run_shift]
  exact lci_run_mono C _ (lci_step_nonneg hC _ _) j

lemma lci_id1 {C : ℝ} (hC : 0 ≤ C) (x b : ℝ) :
    min x (b + C) + lci_step C x b = C + min x b := by
  unfold lci_step
  simp only [min_def, max_def]
  split_ifs <;> linarith

lemma lci_id2 {C x b : ℝ} (hC : 0 ≤ C) (hb : 0 ≤ b) (hx : 0 ≤ x) :
    min C (max 0 (x - b)) + min x b = min x (b + C) := by
  simp only [min_def, max_def]
  split_ifs <;> linarith

lemma lci_id3 {C : ℝ} (hC : 0 ≤ C) (x b : ℝ) :
    min C (max 0 (x - b)) + lci_step C x b ≤ C := by
  unfold lci_step
  simp only [min_def, max_def]
  split_ifs <;> linarith

lemma lci_inv (C : ℝ) (hC : 0 ≤ C) (d u tp : ℕ → ℝ) (k N : ℕ)
    (hu : ∀ m, 0 ≤ u m) (htp : ∀ m, 0 ≤ tp m) (htp0 : tp 0 = 0)
    (htpk : ∀ m, k ≤ m → tp m = 0)
    (hprod : ∀ m < N, u m + tp m ≤ d m) (hplant : ∀ m < N, u m + tp (m + 1) ≤ C) :
    ∀ m ≤ N, (∑ i ∈ Finset.range m, (u i + tp i))
        ≤ ∑ i ∈ Finset.range m, min (d i) (lci_b C d k i + C)
      ∧ (∑ i ∈ Finset.range m, (u i + tp i)) + tp m
          ≤ ∑ i ∈ Finset.range m, min (d i) (lci_b C d k i + C) + lci_b C d k m := by
  intro m hm
  induction m with
  | zero =>
    simp [htp0, lci_b, lci_run]
  | succ m ih =>
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    have hp := hprod m (by omega)
    have hl := hplant m (by omega)
    have hum := hu m
    have htm := htp (m + 1)
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have hA : (∑ i ∈ Finset.range m, (u i + tp i)) + (u m + tp m)
        ≤ (∑ i ∈ Finset.range m, min (d i) (lci_b C d k i + C))
          + min (d m) (lci_b C d k m + C) := by
      have := le_min
        (show (∑ i ∈ Finset.range m, (u i + tp i)) + (u m + tp m)
          - (∑ i ∈ Finset.range m, min (d i) (lci_b C d k i + C)) ≤ d m by linarith)
        (show (∑ i ∈ Finset.range m, (u i + tp i)) + (u m + tp m)
          - (∑ i ∈ Finset.range m, min (d i) (lci_b C d k i + C)) ≤ lci_b C d k m + C by
            linarith)
      linarith
    refine ⟨hA, ?_⟩
    by_cases hk : m + 1 < k
    · have hbm : lci_b C d k m = lci_run C d 0 m := if_pos (by omega)
      have hbm1 : lci_b C d k (m + 1) = lci_step C (d m) (lci_run C d 0 m) := if_pos hk
      rw [hbm1, hbm]
      rw [hbm] at ih2
      have hid := lci_id1 hC (d m) (lci_run C d 0 m)
      have := le_min
        (show (∑ i ∈ Finset.range m, (u i + tp i)) + (u m + tp m) + tp (m + 1)
          - (∑ i ∈ Finset.range m, min (d i) (lci_b C d k i + C)) - C ≤ d m by linarith)
        (show (∑ i ∈ Finset.range m, (u i + tp i)) + (u m + tp m) + tp (m + 1)
          - (∑ i ∈ Finset.range m, min (d i) (lci_b C d k i + C)) - C
            ≤ lci_run C d 0 m by linarith)
      linarith
    · rw [htpk (m + 1) (by omega)]
      have : lci_b C d k (m + 1) = 0 := if_neg hk
      rw [this]
      linarith

lemma lci_rot_val (n : ℕ) (i : Fin n) (h : i.val + 1 < n) :
    ((finRotate n i : Fin n) : ℕ) = i.val + 1 := by
  cases n with
  | zero => exact i.elim0
  | succ n =>
    rw [coe_finRotate_of_ne_last]
    intro h'
    rw [h'] at h
    simp at h

lemma lci_rot_last (n : ℕ) (i : Fin n) (h : i.val + 1 = n) :
    ((finRotate n i : Fin n) : ℕ) = 0 := by
  cases n with
  | zero => exact i.elim0
  | succ n =>
    have : i = Fin.last n := Fin.ext (by simp; omega)
    subst this
    simp

lemma lci_ext_rot (n : ℕ) (x : Fin n → ℝ) (m : ℕ) (hm : m + 1 < n) :
    lci_ext n (fun i => x (finRotate n i)) m = lci_ext n x (m + 1) := by
  have h1 : m < n := by omega
  simp only [lci_ext, dif_pos h1, dif_pos hm]
  congr 1
  apply Fin.ext
  rw [lci_rot_val n ⟨m, h1⟩ hm]

lemma lci_ext_rot_last (n : ℕ) (x : Fin n → ℝ) (m : ℕ) (hm : m + 1 = n) :
    lci_ext n (fun i => x (finRotate n i)) m = lci_ext n x 0 := by
  have h1 : m < n := by omega
  have h0 : 0 < n := by omega
  simp only [lci_ext, dif_pos h1, dif_pos h0]
  congr 1
  apply Fin.ext
  rw [lci_rot_last n ⟨m, h1⟩ hm]

lemma lci_run_rot (n : ℕ) (C : ℝ) (x : Fin n → ℝ) (a : ℝ) (j : ℕ) (hj : j < n) :
    lci_run C (lci_ext n (fun i => x (finRotate n i))) a j
      = lci_run C (fun m => lci_ext n x (m + 1)) a j :=
  lci_run_congr C _ _ a j (fun m hm => lci_ext_rot n x m (by omega))

lemma lci_f_rot_le (n : ℕ) (C : ℝ) (hC : 0 ≤ C) (x : Fin n → ℝ) (j : ℕ) (hj : j + 1 < n) :
    lci_f C (lci_ext n (fun i => x (finRotate n i))) j ≤ lci_f C (lci_ext n x) (j + 1) := by
  unfold lci_f
  rw [lci_ext_rot n x j hj, lci_run_rot n C x 0 j (by omega)]
  have h1 := lci_run_tail_le C hC (lci_ext n x) j
  have h2 := min_le_min_left (lci_ext n x (j + 1))
    (show lci_run C (fun m => lci_ext n x (m + 1)) 0 j + C ≤ lci_run C (lci_ext n x) 0 (j + 1) + C
      by linarith)
  linarith

lemma lci_V_succ_sub (C : ℝ) (d : ℕ → ℝ) (j n : ℕ) (hj : j < n) :
    lci_V C d (j + 1) n - lci_V C d j n = lci_f C d j := by
  unfold lci_V lci_f
  rw [← Finset.sum_sub_distrib, Finset.sum_eq_single_of_mem j (Finset.mem_range.2 hj)]
  · unfold lci_b
    rw [if_pos (Nat.lt_succ_self j), if_neg (lt_irrefl j), zero_add]
  · intro m _ hm
    unfold lci_b
    by_cases h : m < j
    · rw [if_pos h, if_pos (by omega)]
      ring
    · rw [if_neg h, if_neg (by omega)]
      ring

open SupplyChainTheory in
lemma lci_perf_ge {n : ℕ} (C : ℝ) (x : Fin n → ℝ) (E : Finset (Fin n × Fin n))
    (y : Fin n → Fin n → ℝ) (hy : FlexFeasible C x E y) : ∑ i, ∑ j, y i j ≤ perf C x E := by
  unfold perf
  apply le_csSup
  · refine ⟨∑ i, x i, ?_⟩
    rintro v ⟨z, hz, rfl⟩
    exact Finset.sum_le_sum (fun i _ => hz.2.2.2 i)
  · exact ⟨y, hy, rfl⟩

open SupplyChainTheory in
lemma lci_perf_le {n : ℕ} (C : ℝ) (hC : 0 ≤ C) (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i)
    (E : Finset (Fin n × Fin n)) (B : ℝ)
    (h : ∀ y, FlexFeasible C x E y → ∑ i, ∑ j, y i j ≤ B) : perf C x E ≤ B := by
  unfold perf
  apply csSup_le
  · exact ⟨_, fun _ _ => 0, ⟨fun _ _ => le_rfl, fun _ _ _ => rfl, fun _ => by simp [hC],
      fun i => by simp [hx i]⟩, rfl⟩
  · rintro v ⟨y, hy, rfl⟩
    exact h y hy

open SupplyChainTheory in
lemma lci_perf_nonneg {n : ℕ} (C : ℝ) (hC : 0 ≤ C) (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i)
    (E : Finset (Fin n × Fin n)) : 0 ≤ perf C x E := by
  have := lci_perf_ge C x E (fun _ _ => 0)
    ⟨fun _ _ => le_rfl, fun _ _ _ => rfl, fun _ => by simp [hC], fun i => by simp [hx i]⟩
  simpa using this

open SupplyChainTheory in
lemma lci_perf_le_nC {n : ℕ} (C : ℝ) (hC : 0 ≤ C) (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i)
    (E : Finset (Fin n × Fin n)) : perf C x E ≤ n * C := by
  apply lci_perf_le C hC x hx E
  intro y hy
  rw [Finset.sum_comm]
  calc ∑ j, ∑ i, y i j ≤ ∑ _j : Fin n, C := Finset.sum_le_sum (fun j _ => hy.2.2.1 j)
    _ = n * C := by simp

open SupplyChainTheory in
lemma lci_perf_lip {n : ℕ} (C : ℝ) (hC : 0 ≤ C) (x x' : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i)
    (hx' : ∀ i, 0 ≤ x' i) (E : Finset (Fin n × Fin n)) :
    perf C x E ≤ perf C x' E + ∑ i, |x i - x' i| := by
  apply lci_perf_le C hC x hx E
  intro y hy
  obtain ⟨hnn, hsupp, hcol, hrow⟩ := hy
  have hr0 : ∀ i, 0 ≤ ∑ j, y i j := fun i => Finset.sum_nonneg (fun j _ => hnn i j)
  set θ : Fin n → ℝ := fun i => min (∑ j, y i j) (x' i) / ∑ j, y i j with hθ
  have hθ0 : ∀ i, 0 ≤ θ i := fun i => div_nonneg (le_min (hr0 i) (hx' i)) (hr0 i)
  have hθ1 : ∀ i, θ i ≤ 1 := fun i => div_le_one_of_le₀ (min_le_left _ _) (hr0 i)
  have hrow' : ∀ i, ∑ j, y i j * θ i = min (∑ j, y i j) (x' i) := by
    intro i
    rw [← Finset.sum_mul]
    by_cases h0 : ∑ j, y i j = 0
    · rw [h0, zero_mul, min_eq_left (hx' i)]
    · simp only [hθ]
      field_simp
  have hfeas : FlexFeasible C x' E (fun i j => y i j * θ i) := by
    refine ⟨fun i j => mul_nonneg (hnn i j) (hθ0 i), fun i j hij => by simp [hsupp i j hij],
      fun j => ?_, fun i => ?_⟩
    · calc ∑ i, y i j * θ i ≤ ∑ i, y i j :=
            Finset.sum_le_sum (fun i _ => mul_le_of_le_one_right (hnn i j) (hθ1 i))
        _ ≤ C := hcol j
    · rw [hrow' i]
      exact min_le_right _ _
  have hge := lci_perf_ge C x' E _ hfeas
  have hkey : ∀ i, ∑ j, y i j ≤ min (∑ j, y i j) (x' i) + |x i - x' i| := by
    intro i
    have h1 := hrow i
    have h2 := le_abs_self (x i - x' i)
    have h3 := abs_nonneg (x i - x' i)
    rcases le_total (∑ j, y i j) (x' i) with h | h
    · rw [min_eq_left h]; linarith
    · rw [min_eq_right h]; linarith
  calc ∑ i, ∑ j, y i j ≤ ∑ i, (min (∑ j, y i j) (x' i) + |x i - x' i|) :=
        Finset.sum_le_sum (fun i _ => hkey i)
    _ = ∑ i, ∑ j, y i j * θ i + ∑ i, |x i - x' i| := by
        rw [Finset.sum_add_distrib]
        simp only [hrow']
    _ ≤ perf C x' E + ∑ i, |x i - x' i| := by linarith

open SupplyChainTheory in
lemma lci_perf_cont {n : ℕ} (C : ℝ) (hC : 0 ≤ C) (E : Finset (Fin n × Fin n)) :
    Continuous (fun z : Fin n → ℝ => perf C (fun i => max (z i) 0) E) := by
  apply LipschitzWith.continuous (K := (n : NNReal))
  apply LipschitzWith.of_dist_le_mul
  intro z z'
  rw [Real.dist_eq]
  have hz : ∀ i, 0 ≤ max (z i) 0 := fun i => le_max_right _ _
  have hz' : ∀ i, 0 ≤ max (z' i) 0 := fun i => le_max_right _ _
  have h1 := lci_perf_lip C hC _ _ hz hz' E
  have h2 := lci_perf_lip C hC _ _ hz' hz E
  have h3 : ∑ i, |max (z i) 0 - max (z' i) 0| ≤ n * dist z z' := by
    calc ∑ i, |max (z i) 0 - max (z' i) 0| ≤ ∑ _i : Fin n, dist z z' := by
          apply Finset.sum_le_sum
          intro i _
          exact (abs_max_sub_max_le_abs _ _ _).trans
            (by rw [← Real.dist_eq]; exact dist_le_pi_dist z z' i)
      _ = n * dist z z' := by simp
  have h4 : ∑ i, |max (z' i) 0 - max (z i) 0| = ∑ i, |max (z i) 0 - max (z' i) 0| :=
    Finset.sum_congr rfl (fun i _ => abs_sub_comm _ _)
  push_cast
  rw [abs_le]
  constructor <;> linarith

open SupplyChainTheory in
lemma lci_lower (n : ℕ) (C : ℝ) (hC : 0 ≤ C) (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i)
    (E : Finset (Fin n × Fin n)) (arc : Fin n → Prop) [DecidablePred arc] (b : Fin n → ℝ)
    (hb : ∀ i, 0 ≤ b i) (hb0 : ∀ j, ¬ arc j → b (finRotate n j) = 0)
    (hb1 : ∀ j, arc j → b (finRotate n j) ≤ lci_step C (x j) (b j))
    (hEd : ∀ i, (i, i) ∈ E) (hEa : ∀ j, arc j → (finRotate n j, j) ∈ E) :
    ∑ i, min (x i) (b i + C) ≤ perf C x E := by
  classical
  set U : Fin n → ℝ := fun i => min C (max 0 (x i - b i)) with hU
  set T : Fin n → ℝ := fun i => min (x i) (b i) with hT
  set y : Fin n → Fin n → ℝ := fun i j =>
    (if i = j then U i else 0) + (if i = finRotate n j ∧ arc j then T i else 0) with hy
  have hU0 : ∀ i, 0 ≤ U i := fun i => le_min hC (le_max_left _ _)
  have hT0 : ∀ i, 0 ≤ T i := fun i => le_min (hx i) (hb i)
  have hrow : ∀ i, ∑ j, y i j = min (x i) (b i + C) := by
    intro i
    have h1 : ∑ j, (if i = j then U i else 0) = U i := by simp
    have h2 : ∑ j, (if i = finRotate n j ∧ arc j then T i else 0)
        = if arc ((finRotate n).symm i) then T i else 0 := by
      rw [Finset.sum_eq_single ((finRotate n).symm i)]
      · simp only [Equiv.apply_symm_apply, true_and]
      · intro j _ hj
        rw [if_neg]
        rintro ⟨h, _⟩
        exact hj (by rw [h, Equiv.symm_apply_apply])
      · intro h
        exact absurd (Finset.mem_univ _) h
    simp only [hy, Finset.sum_add_distrib, h1, h2]
    by_cases ha : arc ((finRotate n).symm i)
    · rw [if_pos ha]
      exact lci_id2 hC (hb i) (hx i)
    · rw [if_neg ha]
      have h0 := hb0 _ ha
      rw [Equiv.apply_symm_apply] at h0
      simp only [hU, h0, sub_zero, zero_add, add_zero]
      rw [max_eq_right (hx i), min_comm]
  have hcol : ∀ j, ∑ i, y i j ≤ C := by
    intro j
    have h1 : ∑ i, (if i = j then U i else 0) = U j := by simp
    have h2 : ∑ i, (if i = finRotate n j ∧ arc j then T i else 0)
        = if arc j then T (finRotate n j) else 0 := by
      by_cases ha : arc j
      · simp [ha]
      · simp [ha]
    simp only [hy, Finset.sum_add_distrib, h1, h2]
    by_cases ha : arc j
    · rw [if_pos ha]
      have h3 : T (finRotate n j) ≤ lci_step C (x j) (b j) :=
        (min_le_right _ _).trans (hb1 j ha)
      have h4 := lci_id3 hC (x j) (b j)
      have h5 : U j = min C (max 0 (x j - b j)) := rfl
      linarith
    · rw [if_neg ha, add_zero]
      exact min_le_left _ _
  have hfeas : FlexFeasible C x E y := by
    refine ⟨?_, ?_, hcol, fun i => (hrow i).le.trans (min_le_left _ _)⟩
    · intro i j
      simp only [hy]
      apply add_nonneg
      · split_ifs
        · exact hU0 i
        · exact le_rfl
      · split_ifs
        · exact hT0 i
        · exact le_rfl
    · intro i j hij
      have h1 : ¬ i = j := fun h => hij (by subst h; exact hEd i)
      have h2 : ¬ (i = finRotate n j ∧ arc j) := fun h => hij (by rw [h.1]; exact hEa j h.2)
      simp only [hy, if_neg h1, if_neg h2, add_zero]
  have := lci_perf_ge C x E y hfeas
  simpa only [hrow] using this

open SupplyChainTheory in
lemma lci_upper (n k : ℕ) (hk : k ≤ n) (C : ℝ) (hC : 0 ≤ C) (x : Fin n → ℝ)
    (hx : ∀ i, 0 ≤ x i) :
    perf C x (partialChain n k) ≤ lci_V C (lci_ext n x) k n := by
  classical
  apply lci_perf_le C hC x hx
  intro y hy
  obtain ⟨hnn, hsupp, hcol, hrow⟩ := hy
  have hs : ∀ i j : Fin n, y i j ≠ 0 → i = j ∨ (j.val + 1 < k ∧ i.val = j.val + 1) := by
    intro i j hij
    by_contra hcon
    push Not at hcon
    apply hij
    apply hsupp
    intro hmem
    simp only [partialChain, dedicated, Finset.mem_union, Finset.mem_image, Finset.mem_univ,
      true_and, Finset.mem_filter, Prod.mk.injEq] at hmem
    rcases hmem with ⟨a, rfl, rfl⟩ | ⟨a, ha, rfl, rfl⟩
    · exact hcon.1 rfl
    · exact hcon.2 ha (lci_rot_val n a (by omega))
  set u : ℕ → ℝ := fun m => if h : m < n then y ⟨m, h⟩ ⟨m, h⟩ else 0 with hu
  set tp : ℕ → ℝ := fun m => if h : 0 < m ∧ m < k then y ⟨m, by omega⟩ ⟨m - 1, by omega⟩
    else 0 with htp
  have hrs : ∀ i : Fin n, ∑ j, y i j = u i.val + tp i.val := by
    intro i
    have hpt : ∀ j, y i j = (if j = i then y i j else 0)
        + (if j.val + 1 = i.val ∧ i.val < k then y i j else 0) := by
      intro j
      by_cases hji : j = i
      · subst hji
        simp
      · by_cases hy0 : y i j = 0
        · simp [hy0]
        · rcases hs i j hy0 with h | ⟨h1, h2⟩
          · exact absurd h.symm hji
          · rw [if_neg hji, if_pos ⟨h2.symm, by omega⟩, zero_add]
    rw [Finset.sum_congr rfl (fun j _ => hpt j), Finset.sum_add_distrib]
    have hui : u i.val = y i i := by simp [hu, i.isLt]
    have h1 : ∑ j : Fin n, (if j = i then y i j else 0) = y i i := by simp
    have h2 : ∑ j : Fin n, (if j.val + 1 = i.val ∧ i.val < k then y i j else 0) = tp i.val := by
      by_cases hc : 0 < i.val ∧ i.val < k
      · rw [Finset.sum_eq_single ⟨i.val - 1, by omega⟩]
        · have e1 : ((⟨i.val - 1, by omega⟩ : Fin n) : ℕ) + 1 = i.val := by simp; omega
          rw [if_pos ⟨e1, hc.2⟩]
          simp only [htp, dif_pos hc]
        · intro j _ hj
          rw [if_neg]
          rintro ⟨h1, _⟩
          exact hj (Fin.ext (by simp; omega))
        · intro h
          exact absurd (Finset.mem_univ _) h
      · have e0 : tp i.val = 0 := by simp only [htp, dif_neg hc]
        rw [e0]
        apply Finset.sum_eq_zero
        intro j _
        rw [if_neg]
        rintro ⟨h1, h2⟩
        exact hc ⟨by omega, h2⟩
    rw [h1, h2, hui]
  have hprod : ∀ m < n, u m + tp m ≤ lci_ext n x m := by
    intro m hm
    have := hrs ⟨m, hm⟩
    simp only at this
    rw [← this]
    simp only [lci_ext, dif_pos hm]
    exact hrow _
  have hplant : ∀ m < n, u m + tp (m + 1) ≤ C := by
    intro m hm
    have hum : u m = y ⟨m, hm⟩ ⟨m, hm⟩ := by simp [hu, hm]
    by_cases hc : m + 1 < k
    · have htpm : tp (m + 1) = y ⟨m + 1, by omega⟩ ⟨m, hm⟩ := by
        simp only [htp, dif_pos (show 0 < m + 1 ∧ m + 1 < k from ⟨by omega, hc⟩)]
        rfl
      rw [hum, htpm]
      have hne : (⟨m, hm⟩ : Fin n) ≠ ⟨m + 1, by omega⟩ := by simp
      calc y ⟨m, hm⟩ ⟨m, hm⟩ + y ⟨m + 1, by omega⟩ ⟨m, hm⟩
          = ∑ i ∈ ({⟨m, hm⟩, ⟨m + 1, by omega⟩} : Finset (Fin n)), y i ⟨m, hm⟩ := by
            rw [Finset.sum_pair hne]
        _ ≤ ∑ i, y i ⟨m, hm⟩ :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
              (fun i _ _ => hnn i _)
        _ ≤ C := hcol _
    · have htpm : tp (m + 1) = 0 := by
        simp only [htp]
        rw [dif_neg]
        omega
      rw [hum, htpm, add_zero]
      exact (Finset.single_le_sum (fun i _ => hnn i ⟨m, hm⟩) (Finset.mem_univ _)).trans (hcol _)
  have htot : ∑ i, ∑ j, y i j = ∑ m ∈ Finset.range n, (u m + tp m) := by
    rw [Finset.sum_congr rfl (fun i _ => hrs i)]
    exact Fin.sum_univ_eq_sum_range (fun m => u m + tp m) n
  rw [htot]
  have hu0 : ∀ m, 0 ≤ u m := by
    intro m
    simp only [hu]
    split_ifs
    · exact hnn _ _
    · exact le_rfl
  have htp0' : ∀ m, 0 ≤ tp m := by
    intro m
    simp only [htp]
    split_ifs
    · exact hnn _ _
    · exact le_rfl
  have htpz : tp 0 = 0 := by simp [htp]
  have htpk : ∀ m, k ≤ m → tp m = 0 := by
    intro m hm
    simp only [htp]
    rw [dif_neg]
    omega
  exact (lci_inv C hC (lci_ext n x) u tp k n hu0 htp0' htpz htpk hprod hplant n le_rfl).1

open SupplyChainTheory in
lemma lci_lower_pc (n k : ℕ) (hk : k ≤ n) (C : ℝ) (hC : 0 ≤ C) (x : Fin n → ℝ)
    (hx : ∀ i, 0 ≤ x i) :
    lci_V C (lci_ext n x) k n ≤ perf C x (partialChain n k) := by
  classical
  have hext : ∀ i : Fin n, lci_ext n x i.val = x i := fun i => by simp [lci_ext, i.isLt]
  have h := lci_lower n C hC x hx (partialChain n k) (fun j => j.val + 1 < k)
    (fun i => lci_b C (lci_ext n x) k i.val) ?_ ?_ ?_ ?_ ?_
  · unfold lci_V
    rw [← Fin.sum_univ_eq_sum_range
      (fun m => min (lci_ext n x m) (lci_b C (lci_ext n x) k m + C)) n]
    simpa only [hext] using h
  · intro i
    unfold lci_b
    split_ifs
    · exact lci_run_nonneg hC _ le_rfl _
    · exact le_rfl
  · intro j hj
    by_cases hjn : j.val + 1 < n
    · rw [lci_rot_val n j hjn]
      unfold lci_b
      rw [if_neg hj]
    · rw [lci_rot_last n j (by omega)]
      simp [lci_b, lci_run]
  · intro j hj
    rw [lci_rot_val n j (by omega)]
    unfold lci_b
    rw [if_pos hj, if_pos (by omega)]
    show lci_step C (lci_ext n x j.val) (lci_run C (lci_ext n x) 0 j.val) ≤ _
    rw [hext j]
  · intro i
    simp only [partialChain, dedicated, Finset.mem_union, Finset.mem_image]
    left
    exact ⟨i, Finset.mem_univ _, rfl⟩
  · intro j hj
    simp only [partialChain, Finset.mem_union, Finset.mem_image, Finset.mem_filter]
    right
    exact ⟨j, ⟨Finset.mem_univ _, hj⟩, rfl⟩

open SupplyChainTheory in
lemma lci_pc_eq (n k : ℕ) (hk : k ≤ n) (C : ℝ) (hC : 0 ≤ C) (x : Fin n → ℝ)
    (hx : ∀ i, 0 ≤ x i) :
    perf C x (partialChain n k) = lci_V C (lci_ext n x) k n :=
  le_antisymm (lci_upper n k hk C hC x hx) (lci_lower_pc n k hk C hC x hx)

open SupplyChainTheory in
lemma lci_lower_cyc (n : ℕ) (hn : 2 ≤ n) (C : ℝ) (hC : 0 ≤ C) (x : Fin n → ℝ)
    (hx : ∀ i, 0 ≤ x i) :
    lci_V C (lci_ext n x) n n + lci_f C (lci_ext n (fun i => x (finRotate n i))) (n - 1)
      ≤ perf C x (longChain n) := by
  classical
  have hext : ∀ i : Fin n, lci_ext n x i.val = x i := fun i => by simp [lci_ext, i.isLt]
  have hX0 : 0 ≤ lci_run C (lci_ext n x) 0 n := lci_run_nonneg hC _ le_rfl n
  have h := lci_lower n C hC x hx (longChain n) (fun _ => True)
    (fun i => lci_run C (lci_ext n x) (lci_run C (lci_ext n x) 0 n) i.val)
    (fun i => lci_run_nonneg hC _ hX0 _) (fun j hj => absurd trivial hj) ?_ ?_ ?_
  · refine le_trans ?_ h
    have hsum : ∑ i : Fin n, min (x i)
          (lci_run C (lci_ext n x) (lci_run C (lci_ext n x) 0 n) i.val + C)
        = ∑ m ∈ Finset.range n, min (lci_ext n x m)
          (lci_run C (lci_ext n x) (lci_run C (lci_ext n x) 0 n) m + C) := by
      rw [← Fin.sum_univ_eq_sum_range (fun m => min (lci_ext n x m)
        (lci_run C (lci_ext n x) (lci_run C (lci_ext n x) 0 n) m + C)) n]
      simp only [hext]
    rw [hsum]
    obtain ⟨p, rfl⟩ : ∃ p, n = p + 1 := ⟨n - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    unfold lci_V
    rw [Finset.sum_range_succ', Finset.sum_range_succ']
    have h1 : ∑ m ∈ Finset.range p, min (lci_ext (p + 1) x (m + 1))
          (lci_b C (lci_ext (p + 1) x) (p + 1) (m + 1) + C)
        ≤ ∑ m ∈ Finset.range p, min (lci_ext (p + 1) x (m + 1))
          (lci_run C (lci_ext (p + 1) x) (lci_run C (lci_ext (p + 1) x) 0 (p + 1)) (m + 1) + C) := by
      apply Finset.sum_le_sum
      intro m hm
      rw [Finset.mem_range] at hm
      unfold lci_b
      rw [if_pos (by omega)]
      exact min_le_min_left _ (by linarith [lci_run_mono C (lci_ext (p + 1) x) hX0 (m + 1)])
    have h2 : min (lci_ext (p + 1) x 0) (lci_b C (lci_ext (p + 1) x) (p + 1) 0 + C)
          + lci_f C (lci_ext (p + 1) (fun i => x (finRotate (p + 1) i))) p
        ≤ min (lci_ext (p + 1) x 0)
          (lci_run C (lci_ext (p + 1) x) (lci_run C (lci_ext (p + 1) x) 0 (p + 1)) 0 + C) := by
      have hb0 : lci_b C (lci_ext (p + 1) x) (p + 1) 0 = 0 := by simp [lci_b, lci_run]
      have hr0 : lci_run C (lci_ext (p + 1) x) (lci_run C (lci_ext (p + 1) x) 0 (p + 1)) 0
          = lci_run C (lci_ext (p + 1) x) 0 (p + 1) := rfl
      rw [hb0, hr0]
      unfold lci_f
      rw [lci_ext_rot_last (p + 1) x p rfl, lci_run_rot (p + 1) C x 0 p (by omega)]
      have h3 := lci_run_tail_le C hC (lci_ext (p + 1) x) p
      have h4 := min_le_min_left (lci_ext (p + 1) x 0)
        (show lci_run C (fun m => lci_ext (p + 1) x (m + 1)) 0 p + C
          ≤ lci_run C (lci_ext (p + 1) x) 0 (p + 1) + C by linarith)
      rw [zero_add]
      linarith
    linarith
  · intro j _
    by_cases hjn : j.val + 1 < n
    · rw [lci_rot_val n j hjn]
      show lci_step C (lci_ext n x j.val) (lci_run C (lci_ext n x) _ j.val) ≤ _
      rw [hext j]
    · have hjl : j.val + 1 = n := by omega
      rw [lci_rot_last n j hjl]
      calc lci_run C (lci_ext n x) (lci_run C (lci_ext n x) 0 n) 0
          = lci_run C (lci_ext n x) 0 n := rfl
        _ ≤ lci_run C (lci_ext n x) (lci_run C (lci_ext n x) 0 n) n :=
            lci_run_mono C _ hX0 n
        _ = lci_run C (lci_ext n x) (lci_run C (lci_ext n x) 0 n) (j.val + 1) := by rw [hjl]
        _ = lci_step C (x j) (lci_run C (lci_ext n x) (lci_run C (lci_ext n x) 0 n) j.val) := by
            show lci_step C (lci_ext n x j.val) _ = _
            rw [hext j]
  · intro i
    simp only [longChain, dedicated, Finset.mem_union, Finset.mem_image]
    left
    exact ⟨i, Finset.mem_univ _, rfl⟩
  · intro j _
    simp only [longChain, Finset.mem_union, Finset.mem_image]
    right
    exact ⟨j, Finset.mem_univ _, rfl⟩

lemma lci_ext_cont (n m : ℕ) : Continuous (fun x : Fin n → ℝ => lci_ext n x m) := by
  by_cases h : m < n
  · simp only [lci_ext, dif_pos h]
    exact continuous_apply _
  · simp only [lci_ext, dif_neg h]
    exact continuous_const

lemma lci_run_cont (n : ℕ) (C a : ℝ) (j : ℕ) :
    Continuous (fun x : Fin n → ℝ => lci_run C (lci_ext n x) a j) := by
  induction j with
  | zero => exact continuous_const
  | succ j ih =>
    simp only [lci_run, lci_step]
    exact continuous_const.min (continuous_const.max
      ((continuous_const.add ih).sub (lci_ext_cont n j)))

lemma lci_f_cont (n : ℕ) (C : ℝ) (j : ℕ) :
    Continuous (fun x : Fin n → ℝ => lci_f C (lci_ext n x) j) := by
  simp only [lci_f]
  exact ((lci_ext_cont n j).min ((lci_run_cont n C 0 j).add continuous_const)).sub
    ((lci_ext_cont n j).min continuous_const)

open MeasureTheory SupplyChainTheory in
lemma lci_int {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {n : ℕ}
    (S : BalancedSystem P n) (E : Finset (Fin n × Fin n)) :
    Integrable (fun ω => perf S.C (fun i => S.D i ω) E) P := by
  have hD : Measurable (fun ω => fun i => S.D i ω) := measurable_pi_lambda _ S.measurable_D
  have heq : (fun ω => perf S.C (fun i => S.D i ω) E)
      = (fun z : Fin n → ℝ => perf S.C (fun i => max (z i) 0) E) ∘ (fun ω i => S.D i ω) := by
    funext ω
    simp only [Function.comp_apply]
    congr 1
    funext i
    exact (max_eq_left (S.D_nonneg i ω)).symm
  refine Integrable.of_bound ?_ (n * S.C) ?_
  · rw [heq]
    exact ((lci_perf_cont S.C S.C_nonneg E).measurable.comp hD).aestronglyMeasurable
  · filter_upwards with ω
    rw [Real.norm_eq_abs, abs_le]
    have h0 := lci_perf_nonneg S.C S.C_nonneg (fun i => S.D i ω) (fun i => S.D_nonneg i ω) E
    have h1 := lci_perf_le_nC S.C S.C_nonneg (fun i => S.D i ω) (fun i => S.D_nonneg i ω) E
    have h2 : 0 ≤ (n : ℝ) * S.C := mul_nonneg (Nat.cast_nonneg _) S.C_nonneg
    constructor <;> linarith

open MeasureTheory SupplyChainTheory in
lemma lci_exch {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ} (S : BalancedSystem P n)
    (F : (Fin n → ℝ) → ℝ) (hF : Continuous F) (σ : Equiv.Perm (Fin n)) :
    ∫ ω, F (fun i => S.D (σ i) ω) ∂P = ∫ ω, F (fun i => S.D i ω) ∂P := by
  have hD : Measurable (fun ω => fun i => S.D i ω) := measurable_pi_lambda _ S.measurable_D
  have hDσ : Measurable (fun ω => fun i => S.D (σ i) ω) :=
    measurable_pi_lambda _ (fun i => S.measurable_D (σ i))
  have h1 : ∫ y, F y ∂(P.map (fun ω i => S.D (σ i) ω)) = ∫ ω, F (fun i => S.D (σ i) ω) ∂P :=
    integral_map hDσ.aemeasurable hF.aestronglyMeasurable
  have h2 : ∫ y, F y ∂(P.map (fun ω i => S.D i ω)) = ∫ ω, F (fun i => S.D i ω) ∂P :=
    integral_map hD.aemeasurable hF.aestronglyMeasurable
  rw [← h1, ← h2, S.exchangeable σ]

open MeasureTheory SupplyChainTheory in
lemma lci_exch_int {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}
    (S : BalancedSystem P n) (F : (Fin n → ℝ) → ℝ) (hF : Continuous F) (σ : Equiv.Perm (Fin n))
    (hI : Integrable (fun ω => F (fun i => S.D i ω)) P) :
    Integrable (fun ω => F (fun i => S.D (σ i) ω)) P := by
  have hD : Measurable (fun ω => fun i => S.D i ω) := measurable_pi_lambda _ S.measurable_D
  have hDσ : Measurable (fun ω => fun i => S.D (σ i) ω) :=
    measurable_pi_lambda _ (fun i => S.measurable_D (σ i))
  have h1 : Integrable F (P.map (fun ω i => S.D i ω)) :=
    (integrable_map_measure hF.aestronglyMeasurable hD.aemeasurable).mpr hI
  rw [← S.exchangeable σ] at h1
  exact (integrable_map_measure hF.aestronglyMeasurable hDσ.aemeasurable).mp h1


noncomputable def lco_G (C : ℝ) (n : ℕ) (x : Fin n → ℝ) : ℝ :=
  min (lci_ext n x (n - 1)) (lci_run C (lci_ext n x) 0 (n - 1) + C)

noncomputable def lco_per (n : ℕ) (x : Fin n → ℝ) (m : ℕ) : ℝ := lci_ext n x (m % n)

lemma lco_run_add (C : ℝ) (d : ℕ → ℝ) (a : ℝ) (i j : ℕ) :
    lci_run C d a (i + j) = lci_run C (fun t => d (t + i)) (lci_run C d a i) j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    show lci_step C (d (i + j)) (lci_run C d a (i + j))
      = lci_step C (d (j + i)) (lci_run C (fun t => d (t + i)) (lci_run C d a i) j)
    rw [ih, Nat.add_comm i j]

lemma lco_run_le (C : ℝ) (hC : 0 ≤ C) (d : ℕ → ℝ) (j : ℕ) : lci_run C d 0 j ≤ C := by
  cases j with
  | zero => exact hC
  | succ j =>
    show lci_step C (d j) (lci_run C d 0 j) ≤ C
    unfold lci_step
    exact min_le_left _ _

lemma lco_G_abs (C : ℝ) (hC : 0 ≤ C) (n : ℕ) (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i) :
    |lco_G C n x| ≤ 2 * C := by
  unfold lco_G
  have h1 : 0 ≤ lci_ext n x (n - 1) := by
    unfold lci_ext
    split_ifs
    · exact hx _
    · exact le_rfl
  have h2 := lci_run_nonneg hC (lci_ext n x) (le_refl (0 : ℝ)) (n - 1)
  have h3 := lco_run_le C hC (lci_ext n x) (n - 1)
  rw [abs_le]
  constructor
  · have := le_min h1 (show 0 ≤ lci_run C (lci_ext n x) 0 (n - 1) + C by linarith)
    linarith
  · have := min_le_right (lci_ext n x (n - 1)) (lci_run C (lci_ext n x) 0 (n - 1) + C)
    linarith

lemma lco_G_cont (C : ℝ) (n : ℕ) : Continuous (fun x : Fin n → ℝ => lco_G C n x) := by
  simp only [lco_G]
  exact (lci_ext_cont n (n - 1)).min ((lci_run_cont n C 0 (n - 1)).add continuous_const)

lemma lco_rot_val (n : ℕ) (i : Fin n) : ((finRotate n i : Fin n) : ℕ) = (i.val + 1) % n := by
  by_cases h : i.val + 1 < n
  · rw [lci_rot_val n i h, Nat.mod_eq_of_lt h]
  · have h' : i.val + 1 = n := by omega
    rw [lci_rot_last n i h', h', Nat.mod_self]

lemma lco_rp_val (n : ℕ) (k : ℕ) (i : Fin n) :
    ((((finRotate n) ^ k) i : Fin n) : ℕ) = (i.val + k) % n := by
  induction k generalizing i with
  | zero => simp [Nat.mod_eq_of_lt i.isLt]
  | succ k ih =>
    rw [pow_succ, Equiv.Perm.mul_apply, ih, lco_rot_val, Nat.mod_add_mod,
      show i.val + 1 + k = i.val + (k + 1) by omega]

lemma lco_rp_n (n : ℕ) : (finRotate n) ^ n = 1 := by
  apply Equiv.ext
  intro i
  apply Fin.ext
  rw [lco_rp_val, Equiv.Perm.one_apply, Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]

lemma lco_rp_add_n (n k : ℕ) : (finRotate n) ^ (k + n) = (finRotate n) ^ k := by
  rw [pow_add, lco_rp_n, mul_one]

lemma lco_rp_comm (n j : ℕ) (a : Fin n) :
    ((finRotate n) ^ j) (finRotate n a) = finRotate n (((finRotate n) ^ j) a) := by
  show ((finRotate n) ^ j * finRotate n) a = (finRotate n * (finRotate n) ^ j) a
  rw [← pow_succ, ← pow_succ']

open SupplyChainTheory in
lemma lco_mem_LC (n : ℕ) (a b : Fin n) :
    (a, b) ∈ longChain n ↔ (a = b ∨ a = finRotate n b) := by
  unfold longChain dedicated
  rw [Finset.mem_union, Finset.mem_image, Finset.mem_image]
  constructor
  · rintro (⟨c, _, hc⟩ | ⟨c, _, hc⟩)
    · rw [Prod.mk.injEq] at hc
      left
      rw [← hc.1, ← hc.2]
    · rw [Prod.mk.injEq] at hc
      right
      rw [← hc.1, ← hc.2]
  · rintro (h | h)
    · left
      exact ⟨a, Finset.mem_univ _, by rw [h]⟩
    · right
      exact ⟨b, Finset.mem_univ _, by rw [h]⟩

open SupplyChainTheory in
lemma lco_perf_perm_le {n : ℕ} (C : ℝ) (hC : 0 ≤ C) (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i)
    (E : Finset (Fin n × Fin n)) (σ : Equiv.Perm (Fin n))
    (hE : ∀ i j, (σ i, σ j) ∈ E → (i, j) ∈ E) :
    perf C x E ≤ perf C (fun i => x (σ i)) E := by
  apply lci_perf_le C hC x hx E
  intro y hy
  obtain ⟨hnn, hsupp, hcol, hrow⟩ := hy
  have hfeas : FlexFeasible C (fun i => x (σ i)) E (fun i j => y (σ i) (σ j)) := by
    refine ⟨fun i j => hnn _ _, fun i j hij => hsupp _ _ (fun h => hij (hE i j h)),
      fun j => ?_, fun i => ?_⟩
    · exact (Equiv.sum_comp σ (fun i => y i (σ j))).trans_le (hcol (σ j))
    · exact (Equiv.sum_comp σ (fun j => y (σ i) j)).trans_le (hrow (σ i))
  have hge := lci_perf_ge C (fun i => x (σ i)) E _ hfeas
  have hsum : ∑ i, ∑ j, y (σ i) (σ j) = ∑ i, ∑ j, y i j := by
    calc ∑ i, ∑ j, y (σ i) (σ j) = ∑ i, ∑ j, y (σ i) j :=
          Finset.sum_congr rfl (fun i _ => Equiv.sum_comp σ (fun j => y (σ i) j))
      _ = ∑ i, ∑ j, y i j := Equiv.sum_comp σ (fun i => ∑ j, y i j)
  linarith

open SupplyChainTheory in
lemma lco_perf_rp (n : ℕ) (C : ℝ) (hC : 0 ≤ C) (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i) (j : ℕ) :
    perf C (fun i => x (((finRotate n) ^ j) i)) (longChain n) = perf C x (longChain n) := by
  set σ : Equiv.Perm (Fin n) := (finRotate n) ^ j with hσ
  have hcomm : ∀ a, σ (finRotate n a) = finRotate n (σ a) := lco_rp_comm n j
  have hcomm' : ∀ a, σ.symm (finRotate n a) = finRotate n (σ.symm a) := by
    intro a
    apply σ.injective
    rw [hcomm, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  have hE1 : ∀ i j, (σ i, σ j) ∈ longChain n → (i, j) ∈ longChain n := by
    intro i j h
    rw [lco_mem_LC] at h ⊢
    rcases h with h | h
    · left
      exact σ.injective h
    · right
      rw [← hcomm] at h
      exact σ.injective h
  have hE2 : ∀ i j, (σ.symm i, σ.symm j) ∈ longChain n → (i, j) ∈ longChain n := by
    intro i j h
    rw [lco_mem_LC] at h ⊢
    rcases h with h | h
    · left
      exact σ.symm.injective h
    · right
      rw [← hcomm'] at h
      exact σ.symm.injective h
  apply le_antisymm
  · have := lco_perf_perm_le C hC (fun i => x (σ i)) (fun i => hx _) (longChain n) σ.symm hE2
    simpa only [Equiv.apply_symm_apply] using this
  · exact lco_perf_perm_le C hC x hx _ σ hE1

lemma lco_sum_shift (h : ℕ → ℝ) (n : ℕ) (hp : ∀ k, h (k + n) = h k) (j : ℕ) :
    ∑ k ∈ Finset.range n, h (k + j) = ∑ k ∈ Finset.range n, h k := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have h1 := Finset.sum_range_succ' (fun k => h (k + j)) n
    have h2 := Finset.sum_range_succ (fun k => h (k + j)) n
    have h3 : h (n + j) = h (0 + j) := by rw [Nat.zero_add, Nat.add_comm, hp]
    have h4 : ∑ k ∈ Finset.range n, h (k + (j + 1)) = ∑ k ∈ Finset.range n, h (k + 1 + j) :=
      Finset.sum_congr rfl (fun k _ => by rw [show k + (j + 1) = k + 1 + j by omega])
    rw [h4]
    linarith

lemma lco_per_lt (n : ℕ) (x : Fin n → ℝ) (m : ℕ) (hm : m < n) : lco_per n x m = lci_ext n x m := by
  unfold lco_per
  rw [Nat.mod_eq_of_lt hm]

lemma lco_per_add (n : ℕ) (x : Fin n → ℝ) (m : ℕ) : lco_per n x (m + n) = lco_per n x m := by
  unfold lco_per
  rw [Nat.add_mod_right]

lemma lco_ext_rp (n : ℕ) (x : Fin n → ℝ) (k t : ℕ) (ht : t < n) :
    lci_ext n (fun i => x (((finRotate n) ^ k) i)) t = lco_per n x (t + k) := by
  have hn : 0 < n := by omega
  unfold lco_per lci_ext
  rw [dif_pos ht, dif_pos (Nat.mod_lt _ hn)]
  beta_reduce
  congr 1
  apply Fin.ext
  rw [lco_rp_val]

lemma lco_hper (n : ℕ) (C : ℝ) (x : Fin n → ℝ) (k : ℕ) :
    lco_G C n (fun i => x (((finRotate n) ^ (k + n)) i))
      = lco_G C n (fun i => x (((finRotate n) ^ k) i)) := by
  rw [lco_rp_add_n]

lemma lco_term (n : ℕ) (hn : 0 < n) (C : ℝ) (x : Fin n → ℝ) (m : ℕ) :
    lco_G C n (fun i => x (((finRotate n) ^ (m + 1)) i))
      = min (lco_per n x m) (lci_run C (fun t => lco_per n x (t + (m + 1))) 0 (n - 1) + C) := by
  unfold lco_G
  rw [lco_ext_rp n x (m + 1) (n - 1) (by omega),
    lci_run_congr C (lci_ext n (fun i => x (((finRotate n) ^ (m + 1)) i)))
      (fun t => lco_per n x (t + (m + 1))) 0 (n - 1)
      (fun t ht => lco_ext_rp n x (m + 1) t (by omega)),
    show n - 1 + (m + 1) = m + n by omega, lco_per_add]

lemma lco_sum_eq (n : ℕ) (hn : 0 < n) (C : ℝ) (x : Fin n → ℝ) :
    ∑ k ∈ Finset.range n, lco_G C n (fun i => x (((finRotate n) ^ k) i))
      = ∑ m ∈ Finset.range n,
          min (lco_per n x m) (lci_run C (fun t => lco_per n x (t + (m + 1))) 0 (n - 1) + C) := by
  calc ∑ k ∈ Finset.range n, lco_G C n (fun i => x (((finRotate n) ^ k) i))
      = ∑ k ∈ Finset.range n, lco_G C n (fun i => x (((finRotate n) ^ (k + 1)) i)) :=
        (lco_sum_shift (fun k => lco_G C n (fun i => x (((finRotate n) ^ k) i))) n
          (lco_hper n C x) 1).symm
    _ = _ := Finset.sum_congr rfl (fun m _ => lco_term n hn C x m)

lemma lco_inv (C : ℝ) (hC : 0 ≤ C) (d u tp : ℕ → ℝ) (k N : ℕ)
    (hu : ∀ m, 0 ≤ u m) (htp : ∀ m, 0 ≤ tp m)
    (htpk : ∀ m, k ≤ m → tp m = 0)
    (hprod : ∀ m < N, u m + tp m ≤ d m) (hplant : ∀ m < N, u m + tp (m + 1) ≤ C) :
    ∀ m ≤ N, (∑ i ∈ Finset.range m, (u i + tp i))
        ≤ ∑ i ∈ Finset.range m, min (d i) (lci_b C d k i + C) + tp 0
      ∧ (∑ i ∈ Finset.range m, (u i + tp i)) + tp m
          ≤ ∑ i ∈ Finset.range m, min (d i) (lci_b C d k i + C) + lci_b C d k m + tp 0 := by
  intro m hm
  induction m with
  | zero =>
    have hb0 : lci_b C d k 0 = 0 := by
      unfold lci_b
      split_ifs <;> rfl
    simp only [Finset.range_zero, Finset.sum_empty, hb0]
    have := htp 0
    constructor <;> linarith
  | succ m ih =>
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    have hp := hprod m (by omega)
    have hl := hplant m (by omega)
    have hum := hu m
    have htm := htp (m + 1)
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have hA : (∑ i ∈ Finset.range m, (u i + tp i)) + (u m + tp m)
        ≤ (∑ i ∈ Finset.range m, min (d i) (lci_b C d k i + C))
          + min (d m) (lci_b C d k m + C) + tp 0 := by
      have := le_min
        (show (∑ i ∈ Finset.range m, (u i + tp i)) + (u m + tp m)
          - (∑ i ∈ Finset.range m, min (d i) (lci_b C d k i + C)) - tp 0 ≤ d m by linarith)
        (show (∑ i ∈ Finset.range m, (u i + tp i)) + (u m + tp m)
          - (∑ i ∈ Finset.range m, min (d i) (lci_b C d k i + C)) - tp 0
            ≤ lci_b C d k m + C by linarith)
      linarith
    refine ⟨hA, ?_⟩
    by_cases hk : m + 1 < k
    · have hbm : lci_b C d k m = lci_run C d 0 m := if_pos (by omega)
      have hbm1 : lci_b C d k (m + 1) = lci_step C (d m) (lci_run C d 0 m) := if_pos hk
      rw [hbm1, hbm]
      rw [hbm] at ih2
      have hid := lci_id1 hC (d m) (lci_run C d 0 m)
      have := le_min
        (show (∑ i ∈ Finset.range m, (u i + tp i)) + (u m + tp m) + tp (m + 1)
          - (∑ i ∈ Finset.range m, min (d i) (lci_b C d k i + C)) - C - tp 0 ≤ d m by linarith)
        (show (∑ i ∈ Finset.range m, (u i + tp i)) + (u m + tp m) + tp (m + 1)
          - (∑ i ∈ Finset.range m, min (d i) (lci_b C d k i + C)) - C - tp 0
            ≤ lci_run C d 0 m by linarith)
      linarith
    · rw [htpk (m + 1) (by omega)]
      have : lci_b C d k (m + 1) = 0 := if_neg hk
      rw [this]
      linarith

open SupplyChainTheory in
lemma lco_cyc_upper2 (n : ℕ) (hn : 2 ≤ n) (C : ℝ) (hC : 0 ≤ C) (x : Fin n → ℝ)
    (hx : ∀ i, 0 ≤ x i) (h0 : lci_run C (lci_ext n x) 0 n = 0) :
    perf C x (longChain n) ≤ lci_V C (lci_ext n x) n n := by
  classical
  apply lci_perf_le C hC x hx
  intro y hy
  obtain ⟨hnn, hsupp, hcol, hrow⟩ := hy
  have hne : ∀ j : Fin n, finRotate n j ≠ j := by
    intro j h
    have hv := congrArg Fin.val h
    by_cases hj : j.val + 1 < n
    · rw [lci_rot_val n j hj] at hv
      omega
    · rw [lci_rot_last n j (by omega)] at hv
      omega
  have hs : ∀ i j : Fin n, y i j ≠ 0 → i = j ∨ i = finRotate n j := by
    intro i j hij
    by_contra hcon
    exact hij (hsupp i j (fun hmem => hcon ((lco_mem_LC n i j).1 hmem)))
  have hrs : ∀ i : Fin n, ∑ j, y i j = y i i + y i ((finRotate n).symm i) := by
    intro i
    have hne' : i ≠ (finRotate n).symm i :=
      fun h => hne i ((Equiv.eq_symm_apply (finRotate n)).1 h)
    calc ∑ j, y i j = ∑ j ∈ ({i, (finRotate n).symm i} : Finset (Fin n)), y i j := by
          symm
          apply Finset.sum_subset (Finset.subset_univ _)
          intro j _ hj
          by_contra hyj
          apply hj
          rw [Finset.mem_insert, Finset.mem_singleton]
          rcases hs i j hyj with h | h
          · left
            exact h.symm
          · right
            rw [h, Equiv.symm_apply_apply]
      _ = y i i + y i ((finRotate n).symm i) := Finset.sum_pair hne'
  set u : ℕ → ℝ := fun m => if h : m < n then y ⟨m, h⟩ ⟨m, h⟩ else 0 with hu_def
  set tp : ℕ → ℝ := fun m => if h : m < n then y ⟨m, h⟩ ((finRotate n).symm ⟨m, h⟩)
    else if m = n then y ⟨0, by omega⟩ ((finRotate n).symm ⟨0, by omega⟩) else 0 with htp_def
  have htpsucc : ∀ m (hm : m < n), tp (m + 1) = y (finRotate n ⟨m, hm⟩) ⟨m, hm⟩ := by
    intro m hm
    by_cases h : m + 1 < n
    · have e : finRotate n ⟨m, hm⟩ = ⟨m + 1, h⟩ := Fin.ext (lci_rot_val n ⟨m, hm⟩ h)
      simp only [htp_def, dif_pos h]
      rw [← e, Equiv.symm_apply_apply]
    · have h' : m + 1 = n := by omega
      have e : finRotate n ⟨m, hm⟩ = ⟨0, by omega⟩ := Fin.ext (lci_rot_last n ⟨m, hm⟩ h')
      simp only [htp_def, dif_neg h, if_pos h']
      rw [← e, Equiv.symm_apply_apply]
  have htpn : tp n = tp 0 := by
    have a : tp n = y ⟨0, by omega⟩ ((finRotate n).symm ⟨0, by omega⟩) := by
      simp only [htp_def]
      split_ifs
      all_goals first | rfl | (exfalso; omega)
    have b : tp 0 = y ⟨0, by omega⟩ ((finRotate n).symm ⟨0, by omega⟩) := by
      simp only [htp_def]
      rw [dif_pos (by omega)]
    rw [a, b]
  have hrs' : ∀ m (hm : m < n), ∑ j, y ⟨m, hm⟩ j = u m + tp m := by
    intro m hm
    rw [hrs]
    simp only [hu_def, htp_def, dif_pos hm]
  have hprod : ∀ m < n, u m + tp m ≤ lci_ext n x m := by
    intro m hm
    rw [← hrs' m hm]
    simp only [lci_ext, dif_pos hm]
    exact hrow _
  have hplant : ∀ m < n, u m + tp (m + 1) ≤ C := by
    intro m hm
    rw [htpsucc m hm]
    have hum : u m = y ⟨m, hm⟩ ⟨m, hm⟩ := by simp [hu_def, hm]
    rw [hum]
    have hne2 : (⟨m, hm⟩ : Fin n) ≠ finRotate n ⟨m, hm⟩ := fun h => hne _ h.symm
    calc y ⟨m, hm⟩ ⟨m, hm⟩ + y (finRotate n ⟨m, hm⟩) ⟨m, hm⟩
        = ∑ i ∈ ({⟨m, hm⟩, finRotate n ⟨m, hm⟩} : Finset (Fin n)), y i ⟨m, hm⟩ := by
          rw [Finset.sum_pair hne2]
      _ ≤ ∑ i, y i ⟨m, hm⟩ :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun i _ _ => hnn i _)
      _ ≤ C := hcol _
  have htot : ∑ i, ∑ j, y i j = ∑ m ∈ Finset.range n, (u m + tp m) := by
    rw [← Fin.sum_univ_eq_sum_range (fun m => u m + tp m) n]
    apply Finset.sum_congr rfl
    intro i _
    exact hrs' i.val i.isLt
  have hu0 : ∀ m, 0 ≤ u m := by
    intro m
    simp only [hu_def]
    split_ifs
    · exact hnn _ _
    · exact le_rfl
  have htp0' : ∀ m, 0 ≤ tp m := by
    intro m
    simp only [htp_def]
    split_ifs
    · exact hnn _ _
    · exact hnn _ _
    · exact le_rfl
  have htpk : ∀ m, n + 1 ≤ m → tp m = 0 := by
    intro m hm
    simp only [htp_def]
    rw [dif_neg (by omega), if_neg (by omega)]
  have key := (lco_inv C hC (lci_ext n x) u tp (n + 1) n hu0 htp0' htpk hprod hplant n le_rfl).2
  have hbn : lci_b C (lci_ext n x) (n + 1) n = 0 := by
    unfold lci_b
    rw [if_pos (by omega)]
    exact h0
  have hV : ∑ i ∈ Finset.range n, min (lci_ext n x i) (lci_b C (lci_ext n x) (n + 1) i + C)
      = lci_V C (lci_ext n x) n n := by
    unfold lci_V
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    unfold lci_b
    rw [if_pos (by omega), if_pos hi]
  rw [htot]
  rw [hbn, hV, htpn] at key
  linarith

open SupplyChainTheory in
lemma lco_LC_one : longChain 1 = partialChain 1 1 := by
  decide

open SupplyChainTheory in
lemma lco_cyc_upper (n : ℕ) (hn : 0 < n) (C : ℝ) (hC : 0 ≤ C) (x : Fin n → ℝ)
    (hx : ∀ i, 0 ≤ x i) (h0 : lci_run C (lci_ext n x) 0 n = 0) :
    perf C x (longChain n) ≤ lci_V C (lci_ext n x) n n := by
  by_cases h1 : n = 1
  · subst h1
    rw [lco_LC_one]
    exact lci_upper 1 1 le_rfl C hC x hx
  · exact lco_cyc_upper2 n (by omega) C hC x hx h0

open SupplyChainTheory in
lemma lco_cyc_lower (n : ℕ) (hn : 0 < n) (C : ℝ) (hC : 0 ≤ C) (x : Fin n → ℝ)
    (hx : ∀ i, 0 ≤ x i) :
    ∑ m ∈ Finset.range n,
        min (lco_per n x m) (lci_run C (fun t => lco_per n x (t + (m + 1))) 0 (n - 1) + C)
      ≤ perf C x (longChain n) := by
  classical
  have hext : ∀ i : Fin n, lci_ext n x i.val = x i := fun i => by simp [lci_ext, i.isLt]
  have hX0 : 0 ≤ lci_run C (lci_ext n x) 0 n := lci_run_nonneg hC _ le_rfl n
  have h := lci_lower n C hC x hx (longChain n) (fun _ => True)
    (fun i => lci_run C (lci_ext n x) (lci_run C (lci_ext n x) 0 n) i.val)
    (fun i => lci_run_nonneg hC _ hX0 _) (fun j hj => absurd trivial hj) ?_ ?_ ?_
  · refine le_trans ?_ h
    have hsum : ∑ i : Fin n, min (x i)
          (lci_run C (lci_ext n x) (lci_run C (lci_ext n x) 0 n) i.val + C)
        = ∑ m ∈ Finset.range n, min (lci_ext n x m)
          (lci_run C (lci_ext n x) (lci_run C (lci_ext n x) 0 n) m + C) := by
      rw [← Fin.sum_univ_eq_sum_range (fun m => min (lci_ext n x m)
        (lci_run C (lci_ext n x) (lci_run C (lci_ext n x) 0 n) m + C)) n]
      simp only [hext]
    rw [hsum]
    apply Finset.sum_le_sum
    intro m hm
    rw [Finset.mem_range] at hm
    rw [lco_per_lt n x m hm]
    apply min_le_min_left
    suffices hsuff : lci_run C (fun t => lco_per n x (t + (m + 1))) 0 (n - 1)
        ≤ lci_run C (lci_ext n x) (lci_run C (lci_ext n x) 0 n) m by linarith
    have hpe : ∀ t, t < n → lci_ext n x t = lco_per n x t :=
      fun t ht => (lco_per_lt n x t ht).symm
    have e1 : lci_run C (lci_ext n x) 0 n = lci_run C (lco_per n x) 0 n :=
      lci_run_congr C _ _ 0 n hpe
    have e2 : lci_run C (lci_ext n x) (lci_run C (lco_per n x) 0 n) m
        = lci_run C (lco_per n x) (lci_run C (lco_per n x) 0 n) m :=
      lci_run_congr C _ _ _ m (fun t ht => hpe t (by omega))
    have e3 : lci_run C (lco_per n x) (lci_run C (lco_per n x) 0 n) m
        = lci_run C (lco_per n x) 0 (n + m) := by
      rw [lco_run_add C (lco_per n x) 0 n m]
      exact lci_run_congr C _ _ _ m (fun t _ => (lco_per_add n x t).symm)
    have e4 : lci_run C (lco_per n x) 0 (n + m)
        = lci_run C (fun t => lco_per n x (t + (m + 1))) (lci_run C (lco_per n x) 0 (m + 1))
          (n - 1) := by
      rw [show n + m = (m + 1) + (n - 1) by omega, lco_run_add]
    rw [e1, e2, e3, e4]
    exact lci_run_mono C _ (lci_run_nonneg hC _ le_rfl _) (n - 1)
  · intro j _
    by_cases hjn : j.val + 1 < n
    · rw [lci_rot_val n j hjn]
      show lci_step C (lci_ext n x j.val) (lci_run C (lci_ext n x) _ j.val) ≤ _
      rw [hext j]
    · have hjl : j.val + 1 = n := by omega
      rw [lci_rot_last n j hjl]
      calc lci_run C (lci_ext n x) (lci_run C (lci_ext n x) 0 n) 0
          = lci_run C (lci_ext n x) 0 n := rfl
        _ ≤ lci_run C (lci_ext n x) (lci_run C (lci_ext n x) 0 n) n :=
            lci_run_mono C _ hX0 n
        _ = lci_run C (lci_ext n x) (lci_run C (lci_ext n x) 0 n) (j.val + 1) := by rw [hjl]
        _ = lci_step C (x j) (lci_run C (lci_ext n x) (lci_run C (lci_ext n x) 0 n) j.val) := by
            show lci_step C (lci_ext n x j.val) _ = _
            rw [hext j]
  · intro i
    simp only [longChain, dedicated, Finset.mem_union, Finset.mem_image]
    left
    exact ⟨i, Finset.mem_univ _, rfl⟩
  · intro j _
    simp only [longChain, Finset.mem_union, Finset.mem_image]
    right
    exact ⟨j, Finset.mem_univ _, rfl⟩

lemma lco_upper_b (n : ℕ) (hn : 0 < n) (C : ℝ) (hC : 0 ≤ C) (x : Fin n → ℝ)
    (h0 : lci_run C (lci_ext n x) 0 n = 0) :
    ∑ m ∈ Finset.range n,
        min (lco_per n x m) (lci_run C (fun t => lco_per n x (t + (m + 1))) 0 (n - 1) + C)
      = lci_V C (lci_ext n x) n n := by
  have hpe : ∀ t, t < n → lci_ext n x t = lco_per n x t :=
    fun t ht => (lco_per_lt n x t ht).symm
  have hp0 : lci_run C (lco_per n x) 0 n = 0 := by
    rw [← lci_run_congr C _ _ 0 n hpe]
    exact h0
  unfold lci_V
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.mem_range] at hm
  have hb : lci_b C (lci_ext n x) n m = lci_run C (lco_per n x) 0 m := by
    unfold lci_b
    rw [if_pos hm]
    exact lci_run_congr C _ _ 0 m (fun t ht => hpe t (by omega))
  have hR : lci_run C (fun t => lco_per n x (t + (m + 1))) 0 (n - 1)
      = lci_run C (lco_per n x) 0 m := by
    have hsplit : n - 1 = (n - 1 - m) + m := by omega
    rw [hsplit, lco_run_add]
    have hz : lci_run C (fun t => lco_per n x (t + (m + 1))) 0 (n - 1 - m) = 0 := by
      apply le_antisymm
      · calc lci_run C (fun t => lco_per n x (t + (m + 1))) 0 (n - 1 - m)
            ≤ lci_run C (fun t => lco_per n x (t + (m + 1)))
                (lci_run C (lco_per n x) 0 (m + 1)) (n - 1 - m) :=
              lci_run_mono C _ (lci_run_nonneg hC _ le_rfl _) _
          _ = lci_run C (lco_per n x) 0 ((m + 1) + (n - 1 - m)) :=
              (lco_run_add C (lco_per n x) 0 (m + 1) (n - 1 - m)).symm
          _ = lci_run C (lco_per n x) 0 n := by rw [show m + 1 + (n - 1 - m) = n by omega]
          _ = 0 := hp0
      · exact lci_run_nonneg hC _ le_rfl _
    rw [hz]
    apply lci_run_congr
    intro t _
    show lco_per n x (t + (n - 1 - m) + (m + 1)) = lco_per n x t
    rw [show t + (n - 1 - m) + (m + 1) = t + n by omega, lco_per_add]
  rw [hR, hb, lco_per_lt n x m hm]

open SupplyChainTheory in
lemma lco_real (n : ℕ) (hn : 0 < n) (C : ℝ) (hC : 0 ≤ C) (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i) :
    perf C x (longChain n)
      = ∑ k ∈ Finset.range n, lco_G C n (fun i => x (((finRotate n) ^ k) i)) := by
  apply le_antisymm
  · by_cases hall : ∀ m < n,
        lco_per n x m ≤ lci_run C (fun t => lco_per n x (t + (m + 1))) 0 (n - 1) + C
    · rw [lco_sum_eq n hn C x]
      have hs : ∑ m ∈ Finset.range n, min (lco_per n x m)
            (lci_run C (fun t => lco_per n x (t + (m + 1))) 0 (n - 1) + C) = ∑ i, x i := by
        rw [Finset.sum_congr rfl (fun m hm => min_eq_left (hall m (Finset.mem_range.1 hm)))]
        rw [← Fin.sum_univ_eq_sum_range (fun m => lco_per n x m) n]
        apply Finset.sum_congr rfl
        intro i _
        rw [lco_per_lt n x i.val i.isLt]
        simp [lci_ext, i.isLt]
      rw [hs]
      apply lci_perf_le C hC x hx
      intro y hy
      exact Finset.sum_le_sum (fun i _ => hy.2.2.2 i)
    · push Not at hall
      obtain ⟨m0, hm0, hlt⟩ := hall
      set x' : Fin n → ℝ := fun i => x (((finRotate n) ^ (m0 + 1)) i) with hx'
      have hx'0 : ∀ i, 0 ≤ x' i := fun i => hx _
      have h0 : lci_run C (lci_ext n x') 0 n = 0 := by
        have e1 : lci_run C (lci_ext n x') 0 n
            = lci_run C (fun t => lco_per n x (t + (m0 + 1))) 0 n :=
          lci_run_congr C _ _ 0 n (fun t ht => lco_ext_rp n x (m0 + 1) t ht)
        have e2 : ∀ (d : ℕ → ℝ) (j : ℕ), lci_run C d 0 (j + 1)
            = lci_step C (d j) (lci_run C d 0 j) := fun _ _ => rfl
        have e3 := e2 (fun t => lco_per n x (t + (m0 + 1))) (n - 1)
        rw [Nat.sub_add_cancel hn] at e3
        rw [e1, e3]
        beta_reduce
        rw [show n - 1 + (m0 + 1) = m0 + n by omega, lco_per_add]
        unfold lci_step
        rw [max_eq_left (by linarith), min_eq_right hC]
      have hsum : ∑ k ∈ Finset.range n, lco_G C n (fun i => x (((finRotate n) ^ k) i))
          = ∑ k ∈ Finset.range n, lco_G C n (fun i => x' (((finRotate n) ^ k) i)) := by
        calc ∑ k ∈ Finset.range n, lco_G C n (fun i => x (((finRotate n) ^ k) i))
            = ∑ k ∈ Finset.range n, lco_G C n (fun i => x (((finRotate n) ^ (k + (m0 + 1))) i)) :=
              (lco_sum_shift (fun k => lco_G C n (fun i => x (((finRotate n) ^ k) i))) n
                (lco_hper n C x) (m0 + 1)).symm
          _ = _ := by
              apply Finset.sum_congr rfl
              intro k _
              simp only [hx']
              congr 1
              funext i
              rw [add_comm k, pow_add, Equiv.Perm.mul_apply]
      rw [hsum, lco_sum_eq n hn C x', lco_upper_b n hn C hC x' h0,
        ← lco_perf_rp n C hC x hx (m0 + 1)]
      exact lco_cyc_upper n hn C hC x' hx'0 h0
  · rw [lco_sum_eq n hn C x]
    exact lco_cyc_lower n hn C hC x hx

lemma lco_V_pred (C : ℝ) (m n : ℕ) (hmn : m + 1 = n) (x : Fin n → ℝ) (z : Fin m → ℝ)
    (hz : ∀ t, t < m → lci_ext m z t = lci_ext n x t) :
    lci_V C (lci_ext m z) m m = lci_V C (lci_ext n x) n n - lco_G C n x := by
  subst hmn
  unfold lci_V lco_G
  rw [Finset.sum_range_succ, Nat.add_sub_cancel]
  have hb : lci_b C (lci_ext (m + 1) x) (m + 1) m = lci_run C (lci_ext (m + 1) x) 0 m :=
    if_pos (Nat.lt_succ_self m)
  rw [hb]
  have hs : ∑ t ∈ Finset.range m, min (lci_ext m z t) (lci_b C (lci_ext m z) m t + C)
      = ∑ t ∈ Finset.range m,
          min (lci_ext (m + 1) x t) (lci_b C (lci_ext (m + 1) x) (m + 1) t + C) := by
    apply Finset.sum_congr rfl
    intro t ht
    rw [Finset.mem_range] at ht
    unfold lci_b
    rw [if_pos ht, if_pos (by omega), hz t ht,
      lci_run_congr C (lci_ext m z) (lci_ext (m + 1) x) 0 t (fun s hs => hz s (by omega))]
  rw [hs]
  ring

open SupplyChainTheory in
lemma lcx_struct {n : ℕ} (A : Finset (Fin n × Fin n)) (hA : TwoFlex A) :
    ∃ σ τ : Equiv.Perm (Fin n), (∀ i, (i, σ i) ∈ A) ∧ (∀ i, (i, τ i) ∈ A) ∧ (∀ i, σ i ≠ τ i)
      ∧ (∀ i j, (i, j) ∈ A → j = σ i ∨ j = τ i) := by
  classical
  obtain ⟨hr, hc⟩ := hA
  have hall : ∀ s : Finset (Fin n),
      s.card ≤ (Finset.univ.filter (fun j => ∃ i ∈ s, (i, j) ∈ A)).card := by
    intro s
    set N := Finset.univ.filter (fun j => ∃ i ∈ s, (i, j) ∈ A) with hN
    have h1 : (A.filter (fun e => e.1 ∈ s)).card = 2 * s.card := by
      rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := s)]
      · rw [Finset.sum_congr rfl (fun i hi => ?_), Finset.sum_const, smul_eq_mul, mul_comm]
        rw [Finset.filter_filter]
        rw [Finset.filter_congr (q := fun e => e.1 = i) (fun e _ => by
          constructor
          · exact fun h => h.2
          · intro h; exact ⟨h ▸ hi, h⟩)]
        exact hr i
      · intro e he
        simp only [Finset.coe_filter, Set.mem_ofPred_eq] at he
        exact he.2
    have h2 : (A.filter (fun e => e.2 ∈ N)).card = 2 * N.card := by
      rw [Finset.card_eq_sum_card_fiberwise (f := Prod.snd) (t := N)]
      · rw [Finset.sum_congr rfl (fun j hj => ?_), Finset.sum_const, smul_eq_mul, mul_comm]
        rw [Finset.filter_filter]
        rw [Finset.filter_congr (q := fun e => e.2 = j) (fun e _ => by
          constructor
          · exact fun h => h.2
          · intro h; exact ⟨h ▸ hj, h⟩)]
        exact hc j
      · intro e he
        simp only [Finset.coe_filter, Set.mem_ofPred_eq] at he
        exact he.2
    have h3 : A.filter (fun e => e.1 ∈ s) ⊆ A.filter (fun e => e.2 ∈ N) := by
      intro e he
      rw [Finset.mem_filter] at he ⊢
      refine ⟨he.1, ?_⟩
      rw [hN, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, e.1, he.2, he.1⟩
    have := Finset.card_le_card h3
    omega
  obtain ⟨f, hfinj, hfA⟩ :=
    (Fintype.all_card_le_filter_rel_iff_exists_injective (fun i j => (i, j) ∈ A)).1
      (fun s => by convert hall s using 2; ext j; simp)
  have hfbij : Function.Bijective f := hfinj.bijective_of_finite
  have hrow2 : ∀ i, ∃ j, (i, j) ∈ A ∧ j ≠ f i := by
    intro i
    have hmem : (i, f i) ∈ A.filter (fun e => e.1 = i) := Finset.mem_filter.2 ⟨hfA i, rfl⟩
    obtain ⟨e, he, hne⟩ := Finset.exists_mem_ne (by rw [hr i]; norm_num) (i, f i)
    rw [Finset.mem_filter] at he
    refine ⟨e.2, ?_, ?_⟩
    · have : e = (i, e.2) := Prod.ext he.2 rfl
      rw [← this]; exact he.1
    · intro h
      apply hne
      exact Prod.ext he.2 h
  choose g hgA hgne using hrow2
  have hrowall : ∀ i j, (i, j) ∈ A → j = f i ∨ j = g i := by
    intro i j hij
    have hsub : ({(i, f i), (i, g i)} : Finset (Fin n × Fin n)) ⊆ A.filter (fun e => e.1 = i) := by
      intro e he
      rw [Finset.mem_insert, Finset.mem_singleton] at he
      rw [Finset.mem_filter]
      rcases he with rfl | rfl
      · exact ⟨hfA i, rfl⟩
      · exact ⟨hgA i, rfl⟩
    have hcard : (A.filter (fun e => e.1 = i)).card ≤
        ({(i, f i), (i, g i)} : Finset (Fin n × Fin n)).card := by
      rw [hr i, Finset.card_pair]
      intro h
      exact hgne i (congrArg Prod.snd h).symm
    have heq := Finset.eq_of_subset_of_card_le hsub hcard
    have hm : (i, j) ∈ A.filter (fun e => e.1 = i) := Finset.mem_filter.2 ⟨hij, rfl⟩
    rw [← heq, Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with h | h
    · left; exact congrArg Prod.snd h
    · right; exact congrArg Prod.snd h
  have hginj : Function.Injective g := by
    intro a b hab
    by_contra hne
    obtain ⟨m, hm⟩ := hfbij.2 (g a)
    have hsub : ({(a, g a), (b, g a)} : Finset (Fin n × Fin n)) ⊆ A.filter (fun e => e.2 = g a) := by
      intro e he
      rw [Finset.mem_insert, Finset.mem_singleton] at he
      rw [Finset.mem_filter]
      rcases he with rfl | rfl
      · exact ⟨hgA a, rfl⟩
      · refine ⟨?_, rfl⟩
        rw [hab]; exact hgA b
    have hcard : (A.filter (fun e => e.2 = g a)).card ≤
        ({(a, g a), (b, g a)} : Finset (Fin n × Fin n)).card := by
      rw [hc (g a), Finset.card_pair]
      intro h
      exact hne (congrArg Prod.fst h)
    have heq := Finset.eq_of_subset_of_card_le hsub hcard
    have hmm : (m, g a) ∈ A.filter (fun e => e.2 = g a) := by
      rw [Finset.mem_filter]
      refine ⟨?_, rfl⟩
      rw [← hm]; exact hfA m
    rw [← heq, Finset.mem_insert, Finset.mem_singleton] at hmm
    rcases hmm with h | h
    · have hma : m = a := congrArg Prod.fst h
      subst hma
      exact hgne m hm.symm
    · have hmb : m = b := congrArg Prod.fst h
      subst hmb
      exact hgne m (hm.trans hab).symm
  refine ⟨Equiv.ofBijective f hfbij, Equiv.ofBijective g hginj.bijective_of_finite,
    fun i => hfA i, fun i => hgA i, fun i => (hgne i).symm, ?_⟩
  intro i j hij
  exact hrowall i j hij

open SupplyChainTheory in
lemma lcx_flow {n k : ℕ} (C : ℝ) (x : Fin n → ℝ) (A : Finset (Fin n × Fin n))
    (y : Fin n → Fin n → ℝ) (hy : FlexFeasible C x A y)
    (w q : Fin k → Fin n) (hw : Function.Injective w) (hq : Function.Injective q)
    (hsup : ∀ t j, (w t, j) ∈ A → ∃ s, q s = j ∧ (t, s) ∈ longChain k) :
    ∑ t, ∑ j, y (w t) j ≤ perf C (fun t => x (w t)) (longChain k) := by
  classical
  obtain ⟨hnn, hsupp, hcol, hrow⟩ := hy
  have hrowq : ∀ t, ∑ j, y (w t) j = ∑ s, y (w t) (q s) := by
    intro t
    rw [← Finset.sum_image (f := fun j => y (w t) j) (fun a _ b _ h => hq h)]
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j _ hj
    by_contra hne
    have hmem : (w t, j) ∈ A := by
      by_contra hA
      exact hne (hsupp _ _ hA)
    obtain ⟨s, hs, _⟩ := hsup t j hmem
    exact hj (Finset.mem_image.2 ⟨s, Finset.mem_univ _, hs⟩)
  have key := lci_perf_ge C (fun t => x (w t)) (longChain k) (fun t s => y (w t) (q s)) ?_
  · calc ∑ t, ∑ j, y (w t) j = ∑ t, ∑ s, y (w t) (q s) :=
          Finset.sum_congr rfl (fun t _ => hrowq t)
      _ ≤ _ := key
  refine ⟨fun t s => hnn _ _, ?_, ?_, ?_⟩
  · intro t s hts
    by_contra hne
    have hmem : (w t, q s) ∈ A := by
      by_contra hA
      exact hne (hsupp _ _ hA)
    obtain ⟨s', hs', hts'⟩ := hsup t (q s) hmem
    rw [hq hs'] at hts'
    exact hts hts'
  · intro s
    calc ∑ t, y (w t) (q s) = ∑ i ∈ Finset.univ.image w, y i (q s) := by
          rw [Finset.sum_image (fun a _ b _ h => hw h)]
      _ ≤ ∑ i, y i (q s) := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun i _ _ => hnn _ _)
      _ ≤ C := hcol _
  · intro t
    rw [← hrowq t]
    exact hrow _

open SupplyChainTheory in
lemma lcx_walk {n : ℕ} (A : Finset (Fin n × Fin n)) (σ τ : Equiv.Perm (Fin n))
    (hall : ∀ i j, (i, j) ∈ A → j = σ i ∨ j = τ i) (i : Fin n) :
    ∀ (t : Fin (Function.minimalPeriod (σ.trans τ.symm) i)) (j : Fin n),
      ((σ.trans τ.symm)^[t.val] i, j) ∈ A →
      ∃ s : Fin (Function.minimalPeriod (σ.trans τ.symm) i),
        σ ((σ.trans τ.symm)^[s.val] i) = j ∧
        (t, s) ∈ longChain (Function.minimalPeriod (σ.trans τ.symm) i) := by
  intro t j hj
  have hkpos : 0 < Function.minimalPeriod (σ.trans τ.symm) i :=
    Nat.lt_of_le_of_lt (Nat.zero_le _) t.isLt
  have hstep : ∀ m, σ ((σ.trans τ.symm)^[m] i) = τ ((σ.trans τ.symm)^[m + 1] i) := by
    intro m
    rw [Function.iterate_succ_apply']
    simp
  rcases hall _ _ hj with h | h
  · exact ⟨t, h.symm, (lco_mem_LC _ t t).2 (Or.inl rfl)⟩
  · by_cases ht : t.val = 0
    · refine ⟨⟨Function.minimalPeriod (σ.trans τ.symm) i - 1, by omega⟩, ?_, ?_⟩
      · rw [h, hstep]
        simp only
        rw [Nat.sub_add_cancel (by omega), Function.iterate_minimalPeriod, ht]
        rfl
      · rw [lco_mem_LC]
        right
        apply Fin.ext
        rw [lco_rot_val]
        simp only
        rw [Nat.sub_add_cancel (by omega), Nat.mod_self, ht]
    · refine ⟨⟨t.val - 1, by omega⟩, ?_, ?_⟩
      · rw [h, hstep]
        simp only
        rw [Nat.sub_add_cancel (by omega)]
      · rw [lco_mem_LC]
        right
        apply Fin.ext
        rw [lco_rot_val]
        simp only
        rw [Nat.sub_add_cancel (by omega), Nat.mod_eq_of_lt t.isLt]

lemma lcx_psum (h : ℕ → ℝ) (k : ℕ) (hp : ∀ t, h (t + k) = h t) (a : ℕ) :
    ∑ t ∈ Finset.range (a * k), h t = a * ∑ t ∈ Finset.range k, h t := by
  have hs : ∀ b t, h (b * k + t) = h t := by
    intro b
    induction b with
    | zero => intro t; simp
    | succ b ih =>
      intro t
      rw [show (b + 1) * k + t = (b * k + t) + k by ring, hp, ih]
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih]
    simp only [hs]
    push_cast
    ring

lemma lcx_dc {n : ℕ} (μ : Equiv.Perm (Fin n)) (r : Fin n → ℝ) :
    (orderOf μ : ℝ) * ∑ i, r i = ∑ i, ((orderOf μ / Function.minimalPeriod μ i : ℕ) : ℝ) *
      ∑ t ∈ Finset.range (Function.minimalPeriod μ i), r (μ^[t] i) := by
  have hper : ∀ i, Function.IsPeriodicPt μ (orderOf μ) i := by
    intro i
    show μ^[orderOf μ] i = i
    rw [Equiv.Perm.iterate_eq_pow, pow_orderOf_eq_one]
    rfl
  have h1 : ∀ t, ∑ i, r (μ^[t] i) = ∑ i, r i := by
    intro t
    rw [Equiv.Perm.iterate_eq_pow]
    exact Equiv.sum_comp (μ ^ t) r
  have h2 : ∑ t ∈ Finset.range (orderOf μ), ∑ i, r (μ^[t] i) = (orderOf μ : ℝ) * ∑ i, r i := by
    rw [Finset.sum_congr rfl (fun t _ => h1 t), Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have h3 : ∀ i, ∑ t ∈ Finset.range (orderOf μ), r (μ^[t] i)
      = ((orderOf μ / Function.minimalPeriod μ i : ℕ) : ℝ) *
        ∑ t ∈ Finset.range (Function.minimalPeriod μ i), r (μ^[t] i) := by
    intro i
    have hd := (hper i).minimalPeriod_dvd
    conv_lhs => rw [← Nat.div_mul_cancel hd]
    apply lcx_psum
    intro t
    rw [Function.iterate_add_apply, Function.iterate_minimalPeriod]
  rw [← h2, Finset.sum_comm]
  exact Finset.sum_congr rfl (fun i _ => h3 i)

open MeasureTheory SupplyChainTheory in
lemma lcx_ext {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n k : ℕ} (S : BalancedSystem P n)
    (F : (Fin k → ℝ) → ℝ) (hF : Continuous F) (w : Fin k → Fin n) (hw : Function.Injective w) :
    ∫ ω, F (fun t => S.D (w t) ω) ∂P
      = ∫ ω, F (fun t => lci_ext n (fun i => S.D i ω) t.val) ∂P := by
  classical
  have hkn : k ≤ n := by simpa using Fintype.card_le_of_injective w hw
  let e : {x : Fin n // x ∈ Set.range (Fin.castLE hkn)} ≃ {x : Fin n // x ∈ Set.range w} :=
    (Equiv.ofInjective _ (Fin.castLE_injective hkn)).symm.trans (Equiv.ofInjective w hw)
  have hσ : ∀ t : Fin k, e.extendSubtype (Fin.castLE hkn t) = w t := by
    intro t
    rw [e.extendSubtype_apply_of_mem (Fin.castLE hkn t) ⟨t, rfl⟩]
    simp [e]
  have h := lci_exch S (fun z : Fin n → ℝ => F (fun t => z (Fin.castLE hkn t)))
    (hF.comp (continuous_pi fun t => continuous_apply _)) e.extendSubtype
  simp only [hσ] at h
  rw [h]
  congr 1
  funext ω
  congr 1
  funext t
  rw [lci_ext, dif_pos (lt_of_lt_of_le t.isLt hkn)]
  rfl

open MeasureTheory SupplyChainTheory in
lemma lcx_G_int {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n k : ℕ} (S : BalancedSystem P n) (w : Fin k → Fin n) :
    Integrable (fun ω => lco_G S.C k (fun t => S.D (w t) ω)) P := by
  have hD : Measurable (fun ω => fun t => S.D (w t) ω) :=
    measurable_pi_lambda _ (fun t => S.measurable_D (w t))
  refine Integrable.of_bound ((lco_G_cont S.C k).measurable.comp hD).aestronglyMeasurable
    (2 * S.C) ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs]
  exact lco_G_abs S.C S.C_nonneg k _ (fun t => S.D_nonneg _ ω)

open MeasureTheory SupplyChainTheory in
lemma lcx_LC {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {n : ℕ}
    (S : BalancedSystem P n) (hn : 0 < n) :
    S.expPerf (longChain n)
      = n * ∫ ω, lco_G S.C n (fun t : Fin n => lci_ext n (fun i => S.D i ω) t.val) ∂P := by
  unfold BalancedSystem.expPerf
  have e1 : ∫ ω, perf S.C (fun i => S.D i ω) (longChain n) ∂P
      = ∫ ω, ∑ s ∈ Finset.range n, lco_G S.C n (fun u => S.D (((finRotate n) ^ s) u) ω) ∂P := by
    apply integral_congr_ae
    filter_upwards with ω
    exact lco_real n hn S.C S.C_nonneg (fun i => S.D i ω) (fun i => S.D_nonneg i ω)
  rw [e1, integral_finsetSum _ (fun s _ => lcx_G_int S _)]
  rw [Finset.sum_congr rfl (fun s _ => lcx_ext S (lco_G S.C n) (lco_G_cont S.C n) _
    (((finRotate n) ^ s).injective))]
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

open MeasureTheory SupplyChainTheory in
lemma lcx_g_mono {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {n : ℕ}
    (S : BalancedSystem P n) (k : ℕ) (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    ∫ ω, lco_G S.C k (fun t : Fin k => lci_ext n (fun i => S.D i ω) t.val) ∂P
      ≤ ∫ ω, lco_G S.C n (fun t : Fin n => lci_ext n (fun i => S.D i ω) t.val) ∂P := by
  have hC := S.C_nonneg
  have hx : ∀ ω, ∀ i, 0 ≤ S.D i ω := fun ω i => S.D_nonneg i ω
  have hdec : ∀ m, 1 ≤ m → m ≤ n → ∀ ω,
      lco_G S.C m (fun t : Fin m => lci_ext n (fun i => S.D i ω) t.val)
        = lci_f S.C (lci_ext n (fun i => S.D i ω)) (m - 1)
          + min (lci_ext n (fun i => S.D i ω) (m - 1)) S.C := by
    intro m hm1 hmn ω
    have hz : ∀ s, s < m → lci_ext m (fun t : Fin m => lci_ext n (fun i => S.D i ω) t.val) s
        = lci_ext n (fun i => S.D i ω) s := by
      intro s hs
      rw [lci_ext, dif_pos hs]
    unfold lco_G lci_f
    rw [hz (m - 1) (by omega), lci_run_congr S.C _ (lci_ext n (fun i => S.D i ω)) 0 (m - 1)
      (fun s hs => hz s (by omega))]
    ring
  have hincI : ∀ j, j < n →
      Integrable (fun ω => lci_f S.C (lci_ext n (fun i => S.D i ω)) j) P := by
    intro j hj
    refine ((lci_int S (partialChain n (j + 1))).sub (lci_int S (partialChain n j))).congr ?_
    filter_upwards with ω
    simp only [Pi.sub_apply]
    rw [lci_pc_eq n (j + 1) (by omega) S.C hC _ (hx ω), lci_pc_eq n j (by omega) S.C hC _ (hx ω)]
    exact lci_V_succ_sub S.C _ j n hj
  have hex : ∀ j, ∫ ω, lci_f S.C (lci_ext n (fun i => S.D (finRotate n i) ω)) j ∂P
      = ∫ ω, lci_f S.C (lci_ext n (fun i => S.D i ω)) j ∂P := fun j =>
    lci_exch S (fun x => lci_f S.C (lci_ext n x) j) (lci_f_cont n S.C j) (finRotate n)
  have hexI : ∀ j, j < n →
      Integrable (fun ω => lci_f S.C (lci_ext n (fun i => S.D (finRotate n i) ω)) j) P :=
    fun j hj => lci_exch_int S (fun x => lci_f S.C (lci_ext n x) j) (lci_f_cont n S.C j)
      (finRotate n) (hincI j hj)
  have hstep : ∀ j, j + 1 < n → ∫ ω, lci_f S.C (lci_ext n (fun i => S.D i ω)) j ∂P
      ≤ ∫ ω, lci_f S.C (lci_ext n (fun i => S.D i ω)) (j + 1) ∂P := by
    intro j hj
    rw [← hex j]
    exact integral_mono (hexI j (by omega)) (hincI (j + 1) hj)
      (fun ω => lci_f_rot_le n S.C hC (fun i => S.D i ω) j hj)
  have hmono : ∀ d j, j + d < n → ∫ ω, lci_f S.C (lci_ext n (fun i => S.D i ω)) j ∂P
      ≤ ∫ ω, lci_f S.C (lci_ext n (fun i => S.D i ω)) (j + d) ∂P := by
    intro d
    induction d with
    | zero => intro j _; exact le_rfl
    | succ d ih =>
      intro j hj
      exact (ih j (by omega)).trans (hstep (j + d) (by omega))
  have hD : Measurable (fun ω => fun i => S.D i ω) := measurable_pi_lambda _ S.measurable_D
  have hminI : ∀ j, Integrable (fun ω => min (lci_ext n (fun i => S.D i ω) j) S.C) P := by
    intro j
    refine Integrable.of_bound
      (((lci_ext_cont n j).min continuous_const).measurable.comp hD).aestronglyMeasurable S.C ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_le]
    have h0 : 0 ≤ lci_ext n (fun i => S.D i ω) j := by
      unfold lci_ext
      split_ifs
      · exact hx ω _
      · exact le_rfl
    constructor
    · have := le_min h0 hC
      linarith
    · exact min_le_right _ _
  have hmin : ∀ j, j < n → ∫ ω, min (lci_ext n (fun i => S.D i ω) j) S.C ∂P
      = ∫ ω, min (lci_ext n (fun i => S.D i ω) 0) S.C ∂P := by
    intro j hj
    have := lcx_ext S (fun z : Fin 1 → ℝ => min (z 0) S.C)
      ((continuous_apply 0).min continuous_const)
      (fun _ => (⟨j, hj⟩ : Fin n)) (fun a b _ => Subsingleton.elim a b)
    have e1 : ∀ ω, lci_ext n (fun i => S.D i ω) j = S.D ⟨j, hj⟩ ω := fun ω => by
      rw [lci_ext, dif_pos hj]
    simp only [e1]
    exact this
  have hval : ∀ m, 1 ≤ m → m ≤ n →
      ∫ ω, lco_G S.C m (fun t : Fin m => lci_ext n (fun i => S.D i ω) t.val) ∂P
        = ∫ ω, lci_f S.C (lci_ext n (fun i => S.D i ω)) (m - 1) ∂P
          + ∫ ω, min (lci_ext n (fun i => S.D i ω) 0) S.C ∂P := by
    intro m hm1 hmn
    rw [← hmin (m - 1) (by omega), ← integral_add (hincI (m - 1) (by omega)) (hminI (m - 1))]
    apply integral_congr_ae
    filter_upwards with ω
    exact hdec m hm1 hmn ω
  rw [hval k hk1 hkn, hval n (by omega) le_rfl]
  have := hmono (n - k) (k - 1) (by omega)
  rw [show k - 1 + (n - k) = n - 1 by omega] at this
  linarith

open SupplyChainTheory in
lemma lcx_twoflex (n : ℕ) (hn : 2 ≤ n) : TwoFlex (longChain n) := by
  classical
  have hrot : ∀ i : Fin n, finRotate n i ≠ i := by
    intro i h
    have hv := congrArg Fin.val h
    rw [lco_rot_val] at hv
    rcases Nat.lt_or_ge (i.val + 1) n with hi | hi
    · rw [Nat.mod_eq_of_lt hi] at hv
      omega
    · have he : i.val + 1 = n := by omega
      rw [he, Nat.mod_self] at hv
      omega
  constructor
  · intro i
    have hf : (longChain n).filter (fun e => e.1 = i) = {(i, i), (i, (finRotate n).symm i)} := by
      ext ⟨a, b⟩
      rw [Finset.mem_filter, lco_mem_LC, Finset.mem_insert, Finset.mem_singleton]
      simp only [Prod.mk.injEq]
      constructor
      · rintro ⟨h | h, rfl⟩
        · exact Or.inl ⟨rfl, h.symm⟩
        · refine Or.inr ⟨rfl, ?_⟩
          rw [h, Equiv.symm_apply_apply]
      · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
        · exact ⟨Or.inl rfl, rfl⟩
        · exact ⟨Or.inr (Equiv.apply_symm_apply _ _).symm, rfl⟩
    rw [hf, Finset.card_pair]
    intro h
    have h2 := congrArg Prod.snd h
    simp only at h2
    apply hrot i
    conv_lhs => rw [h2]
    exact Equiv.apply_symm_apply _ _
  · intro j
    have hf : (longChain n).filter (fun e => e.2 = j) = {(j, j), (finRotate n j, j)} := by
      ext ⟨a, b⟩
      rw [Finset.mem_filter, lco_mem_LC, Finset.mem_insert, Finset.mem_singleton]
      simp only [Prod.mk.injEq]
      constructor
      · rintro ⟨h | h, rfl⟩
        · exact Or.inl ⟨h, rfl⟩
        · exact Or.inr ⟨h, rfl⟩
      · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
        · exact ⟨Or.inl rfl, rfl⟩
        · exact ⟨Or.inr rfl, rfl⟩
    rw [hf, Finset.card_pair]
    intro h
    have h2 := congrArg Prod.fst h
    simp only at h2
    exact hrot j h2.symm

lemma lcx_period {n : ℕ} (μ : Equiv.Perm (Fin n)) (i : Fin n) :
    0 < Function.minimalPeriod μ i
      ∧ Function.Injective (fun t : Fin (Function.minimalPeriod μ i) => μ^[t.val] i) := by
  have hper : i ∈ Function.periodicPts μ := ⟨orderOf μ, orderOf_pos μ, by
    show μ^[orderOf μ] i = i
    rw [Equiv.Perm.iterate_eq_pow, pow_orderOf_eq_one]
    rfl⟩
  refine ⟨Function.minimalPeriod_pos_of_mem_periodicPts hper, ?_⟩
  intro a b hab
  exact Fin.ext (Function.iterate_injOn_Iio_minimalPeriod a.isLt b.isLt hab)

open SupplyChainTheory in
lemma lcx_pw {n : ℕ} (C : ℝ) (hC : 0 ≤ C) (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i)
    (A : Finset (Fin n × Fin n)) (σ τ : Equiv.Perm (Fin n))
    (hall : ∀ i j, (i, j) ∈ A → j = σ i ∨ j = τ i) :
    (orderOf (σ.trans τ.symm) : ℝ) * perf C x A ≤
      ∑ i, ((orderOf (σ.trans τ.symm) / Function.minimalPeriod (σ.trans τ.symm) i : ℕ) : ℝ) *
        ∑ s ∈ Finset.range (Function.minimalPeriod (σ.trans τ.symm) i),
          lco_G C (Function.minimalPeriod (σ.trans τ.symm) i)
            (fun u => x ((σ.trans τ.symm)^[
              (((finRotate (Function.minimalPeriod (σ.trans τ.symm) i)) ^ s) u).val] i)) := by
  classical
  have hLR : (0 : ℝ) < (orderOf (σ.trans τ.symm) : ℝ) := by
    exact_mod_cast orderOf_pos (σ.trans τ.symm)
  have hflow : ∀ y, FlexFeasible C x A y → ∀ i,
      ∑ t ∈ Finset.range (Function.minimalPeriod (σ.trans τ.symm) i),
          ∑ j, y ((σ.trans τ.symm)^[t] i) j
        ≤ ∑ s ∈ Finset.range (Function.minimalPeriod (σ.trans τ.symm) i),
          lco_G C (Function.minimalPeriod (σ.trans τ.symm) i)
            (fun u => x ((σ.trans τ.symm)^[
              (((finRotate (Function.minimalPeriod (σ.trans τ.symm) i)) ^ s) u).val] i)) := by
    intro y hy i
    obtain ⟨hkpos, hwinj⟩ := lcx_period (σ.trans τ.symm) i
    have hqinj : Function.Injective
        (fun t : Fin (Function.minimalPeriod (σ.trans τ.symm) i) =>
          σ ((σ.trans τ.symm)^[t.val] i)) :=
      fun a b hab => hwinj (σ.injective hab)
    rw [← Fin.sum_univ_eq_sum_range (fun t => ∑ j, y ((σ.trans τ.symm)^[t] i) j)]
    have h1 := lcx_flow C x A y hy _ _ hwinj hqinj (lcx_walk A σ τ hall i)
    rw [lco_real _ hkpos C hC _ (fun t => hx _)] at h1
    exact h1
  have hbound : perf C x A ≤ (∑ i, ((orderOf (σ.trans τ.symm) /
      Function.minimalPeriod (σ.trans τ.symm) i : ℕ) : ℝ) *
        ∑ s ∈ Finset.range (Function.minimalPeriod (σ.trans τ.symm) i),
          lco_G C (Function.minimalPeriod (σ.trans τ.symm) i)
            (fun u => x ((σ.trans τ.symm)^[
              (((finRotate (Function.minimalPeriod (σ.trans τ.symm) i)) ^ s) u).val] i)))
      / (orderOf (σ.trans τ.symm) : ℝ) := by
    apply lci_perf_le C hC x hx A
    intro y hy
    rw [le_div_iff₀ hLR, mul_comm, lcx_dc (σ.trans τ.symm) (fun i => ∑ j, y i j)]
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_left (hflow y hy i) (Nat.cast_nonneg _)
  rw [le_div_iff₀ hLR] at hbound
  linarith

open MeasureTheory SupplyChainTheory in
lemma lcx_A {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {n : ℕ}
    (S : BalancedSystem P n) (A : Finset (Fin n × Fin n)) (hA : TwoFlex A) :
    S.expPerf A
      ≤ n * ∫ ω, lco_G S.C n (fun t : Fin n => lci_ext n (fun i => S.D i ω) t.val) ∂P := by
  classical
  obtain ⟨σ, τ, -, -, hne, hall⟩ := lcx_struct A hA
  have hLpos : 0 < orderOf (σ.trans τ.symm) := orderOf_pos _
  have hLR : (0 : ℝ) < (orderOf (σ.trans τ.symm) : ℝ) := by exact_mod_cast hLpos
  have hk2 : ∀ i, 2 ≤ Function.minimalPeriod (σ.trans τ.symm) i := by
    intro i
    have h1 := (lcx_period (σ.trans τ.symm) i).1
    by_contra h
    have h1' : Function.minimalPeriod (σ.trans τ.symm) i = 1 := by omega
    rw [Function.minimalPeriod_eq_one_iff_isFixedPt] at h1'
    have h2 : τ.symm (σ i) = i := h1'
    rw [Equiv.symm_apply_eq] at h2
    exact hne i h2
  have hkn : ∀ i, Function.minimalPeriod (σ.trans τ.symm) i ≤ n := by
    intro i
    have h := Fintype.card_le_of_injective _ (lcx_period (σ.trans τ.symm) i).2
    rw [Fintype.card_fin, Fintype.card_fin] at h
    exact h
  have hdvd : ∀ i, Function.minimalPeriod (σ.trans τ.symm) i ∣ orderOf (σ.trans τ.symm) := by
    intro i
    apply Function.IsPeriodicPt.minimalPeriod_dvd
    show (σ.trans τ.symm)^[orderOf (σ.trans τ.symm)] i = i
    rw [Equiv.Perm.iterate_eq_pow, pow_orderOf_eq_one]
    rfl
  have hwinj : ∀ i (s : ℕ), Function.Injective
      (fun u : Fin (Function.minimalPeriod (σ.trans τ.symm) i) => (σ.trans τ.symm)^[
        (((finRotate (Function.minimalPeriod (σ.trans τ.symm) i)) ^ s) u).val] i) := by
    intro i s a b hab
    exact ((finRotate _) ^ s).injective ((lcx_period (σ.trans τ.symm) i).2 hab)
  have hterm : ∀ i (s : ℕ), ∫ ω, lco_G S.C (Function.minimalPeriod (σ.trans τ.symm) i)
      (fun u => S.D ((σ.trans τ.symm)^[
        (((finRotate (Function.minimalPeriod (σ.trans τ.symm) i)) ^ s) u).val] i) ω) ∂P
      = ∫ ω, lco_G S.C (Function.minimalPeriod (σ.trans τ.symm) i)
          (fun t => lci_ext n (fun i => S.D i ω) t.val) ∂P := by
    intro i s
    exact lcx_ext S (lco_G S.C _) (lco_G_cont S.C _) _ (hwinj i s)
  have hInt : ∀ i, Integrable (fun ω =>
      ∑ s ∈ Finset.range (Function.minimalPeriod (σ.trans τ.symm) i),
        lco_G S.C (Function.minimalPeriod (σ.trans τ.symm) i)
          (fun u => S.D ((σ.trans τ.symm)^[
            (((finRotate (Function.minimalPeriod (σ.trans τ.symm) i)) ^ s) u).val] i) ω)) P :=
    fun i => integrable_finsetSum _ (fun s _ => lcx_G_int S _)
  have hmono := fun i => lcx_g_mono S (Function.minimalPeriod (σ.trans τ.symm) i)
    (by have := hk2 i; omega) (hkn i)
  have hmain : (orderOf (σ.trans τ.symm) : ℝ) * S.expPerf A
      ≤ (orderOf (σ.trans τ.symm) : ℝ) *
        (n * ∫ ω, lco_G S.C n (fun t : Fin n => lci_ext n (fun i => S.D i ω) t.val) ∂P) := by
    unfold BalancedSystem.expPerf
    rw [← integral_const_mul]
    refine (integral_mono ((lci_int S A).const_mul _)
      (integrable_finsetSum _ (fun i _ => (hInt i).const_mul _))
      (fun ω => lcx_pw S.C S.C_nonneg (fun i => S.D i ω) (fun i => S.D_nonneg i ω) A σ τ hall)).trans ?_
    rw [integral_finsetSum _ (fun i _ => (hInt i).const_mul _)]
    calc ∑ i, ∫ ω, ((orderOf (σ.trans τ.symm) / Function.minimalPeriod (σ.trans τ.symm) i : ℕ) : ℝ) *
          ∑ s ∈ Finset.range (Function.minimalPeriod (σ.trans τ.symm) i),
            lco_G S.C (Function.minimalPeriod (σ.trans τ.symm) i)
              (fun u => S.D ((σ.trans τ.symm)^[
                (((finRotate (Function.minimalPeriod (σ.trans τ.symm) i)) ^ s) u).val] i) ω) ∂P
        = ∑ i, (orderOf (σ.trans τ.symm) : ℝ) *
            ∫ ω, lco_G S.C (Function.minimalPeriod (σ.trans τ.symm) i)
              (fun t => lci_ext n (fun i => S.D i ω) t.val) ∂P := by
          apply Finset.sum_congr rfl
          intro i _
          rw [integral_const_mul, integral_finsetSum _ (fun s _ => lcx_G_int S _),
            Finset.sum_congr rfl (fun s _ => hterm i s), Finset.sum_const, Finset.card_range,
            nsmul_eq_mul, ← mul_assoc]
          congr 1
          exact_mod_cast Nat.div_mul_cancel (hdvd i)
      _ ≤ ∑ _i : Fin n, (orderOf (σ.trans τ.symm) : ℝ) *
            ∫ ω, lco_G S.C n (fun t : Fin n => lci_ext n (fun i => S.D i ω) t.val) ∂P := by
          apply Finset.sum_le_sum
          intro i _
          exact mul_le_mul_of_nonneg_left (hmono i) hLR.le
      _ = _ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  exact le_of_mul_le_mul_left hmain hLR

open MeasureTheory SupplyChainTheory in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure P] {n : ℕ} (S : BalancedSystem P n) (hn : 2 ≤ n) :
    TwoFlex (longChain n) ∧ ∀ A : Finset (Fin n × Fin n), TwoFlex A →
      S.expPerf A ≤ S.expPerf (longChain n) := by
  refine ⟨lcx_twoflex n hn, fun A hA => ?_⟩
  rw [lcx_LC S (by omega)]
  exact lcx_A S A hA
