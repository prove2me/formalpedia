-- Prove2me | solution 1 for SupplyChainTheory.long_chain_increments
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-27T16:53:21.236574+00:00
-- url     : https://prove2.me/submissions/1e71009c-dce9-4e58-8aa1-1534bdd96f45

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

open MeasureTheory SupplyChainTheory in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure P] {n : ℕ} (S : BalancedSystem P n) :
    (∀ k, 2 ≤ k → k + 1 ≤ n →
        S.expPerf (partialChain n k) - S.expPerf (partialChain n (k - 1))
          ≤ S.expPerf (partialChain n (k + 1)) - S.expPerf (partialChain n k))
      ∧ (2 ≤ n →
        S.expPerf (partialChain n n) - S.expPerf (partialChain n (n - 1))
          ≤ S.expPerf (longChain n) - S.expPerf (partialChain n n)) := by
  have hC := S.C_nonneg
  have hx : ∀ ω, ∀ i, 0 ≤ S.D i ω := fun ω i => S.D_nonneg i ω
  have hinc : ∀ j, j < n → S.expPerf (partialChain n (j + 1)) - S.expPerf (partialChain n j)
      = ∫ ω, lci_f S.C (lci_ext n (fun i => S.D i ω)) j ∂P := by
    intro j hj
    unfold BalancedSystem.expPerf
    rw [← integral_sub (lci_int S _) (lci_int S _)]
    apply integral_congr_ae
    filter_upwards with ω
    rw [lci_pc_eq n (j + 1) (by omega) S.C hC _ (hx ω), lci_pc_eq n j (by omega) S.C hC _ (hx ω)]
    exact lci_V_succ_sub S.C _ j n hj
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
  refine ⟨fun k hk2 hkn => ?_, fun hn => ?_⟩
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    rw [hinc j (by omega), hinc (j + 1) (by omega), ← hex j]
    apply integral_mono (hexI j (by omega)) (hincI (j + 1) (by omega))
    intro ω
    exact lci_f_rot_le n S.C hC (fun i => S.D i ω) j (by omega)
  · obtain ⟨p, rfl⟩ : ∃ p, n = p + 1 := ⟨n - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    rw [hinc p (by omega), ← hex p]
    unfold BalancedSystem.expPerf
    rw [← integral_sub (lci_int S _) (lci_int S _)]
    apply integral_mono (hexI p (by omega)) ((lci_int S _).sub (lci_int S _))
    intro ω
    have h1 := lci_lower_cyc (p + 1) hn S.C hC (fun i => S.D i ω) (hx ω)
    simp only [Nat.add_sub_cancel] at h1
    simp only [Pi.sub_apply]
    rw [lci_pc_eq (p + 1) (p + 1) le_rfl S.C hC _ (hx ω)]
    linarith
