-- Prove2me | solution 1 for SupplyChainTheory.long_chain_open_chain
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-27T17:25:25.520371+00:00
-- url     : https://prove2.me/submissions/67ab2958-5809-4a59-b792-651f76493f37

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

lemma lci_run_congr (C : ℝ) (d d' : ℕ → ℝ) (a : ℝ) (j : ℕ) (h : ∀ m < j, d m = d' m) :
    lci_run C d a j = lci_run C d' a j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    show lci_step C (d j) (lci_run C d a j) = lci_step C (d' j) (lci_run C d' a j)
    rw [ih (fun m hm => h m (by omega)), h j (by omega)]

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

open MeasureTheory SupplyChainTheory in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure P] {n : ℕ} (S : BalancedSystem P n) (hn : 0 < n) :
    S.expPerf (longChain n)
      = n * (S.subPerf n (openChain n) - S.subPerf (n - 1) (openChain (n - 1))) := by
  have hC := S.C_nonneg
  have hx : ∀ ω, ∀ i, 0 ≤ S.D i ω := fun ω i => S.D_nonneg i ω
  have hD : Measurable (fun ω => fun i => S.D i ω) := measurable_pi_lambda _ S.measurable_D
  have hGc : Continuous (lco_G S.C n) := lco_G_cont S.C n
  have hGI : Integrable (fun ω => lco_G S.C n (fun i => S.D i ω)) P := by
    refine Integrable.of_bound (hGc.measurable.comp hD).aestronglyMeasurable (2 * S.C) ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs]
    exact lco_G_abs S.C hC n _ (hx ω)
  have hGIσ : ∀ σ : Equiv.Perm (Fin n),
      Integrable (fun ω => lco_G S.C n (fun i => S.D (σ i) ω)) P :=
    fun σ => lci_exch_int S (lco_G S.C n) hGc σ hGI
  have hreal : ∀ ω, perf S.C (fun i => S.D i ω) (longChain n)
      = ∑ k ∈ Finset.range n, lco_G S.C n (fun i => S.D (((finRotate n) ^ k) i) ω) :=
    fun ω => lco_real n hn S.C hC (fun i => S.D i ω) (hx ω)
  have h1 : S.expPerf (longChain n) = n * ∫ ω, lco_G S.C n (fun i => S.D i ω) ∂P := by
    unfold BalancedSystem.expPerf
    have e1 : ∫ ω, perf S.C (fun i => S.D i ω) (longChain n) ∂P
        = ∫ ω, ∑ k ∈ Finset.range n, lco_G S.C n (fun i => S.D (((finRotate n) ^ k) i) ω) ∂P := by
      apply integral_congr_ae
      filter_upwards with ω
      exact hreal ω
    rw [e1, integral_finsetSum _ (fun k _ => hGIσ _)]
    rw [Finset.sum_congr rfl (fun k _ => lci_exch S (lco_G S.C n) hGc ((finRotate n) ^ k))]
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hA : S.subPerf n (openChain n)
      = ∫ ω, perf S.C (fun i => S.D i ω) (partialChain n n) ∂P := by
    unfold BalancedSystem.subPerf
    apply integral_congr_ae
    filter_upwards with ω
    have e : S.subDemand n ω = fun i => S.D i ω := by
      funext i
      simp [BalancedSystem.subDemand, i.isLt]
    rw [e]
    rfl
  have hB : S.subPerf (n - 1) (openChain (n - 1))
      = ∫ ω, (perf S.C (fun i => S.D i ω) (partialChain n n)
          - lco_G S.C n (fun i => S.D i ω)) ∂P := by
    unfold BalancedSystem.subPerf
    apply integral_congr_ae
    filter_upwards with ω
    have hz0 : ∀ i, 0 ≤ S.subDemand (n - 1) ω i := by
      intro i
      unfold BalancedSystem.subDemand
      split_ifs
      · exact hx ω _
      · exact le_rfl
    rw [show openChain (n - 1) = partialChain (n - 1) (n - 1) from rfl,
      lci_pc_eq (n - 1) (n - 1) le_rfl S.C hC _ hz0, lci_pc_eq n n le_rfl S.C hC _ (hx ω)]
    apply lco_V_pred S.C (n - 1) n (by omega)
    intro t ht
    have htn : t < n := by omega
    simp [lci_ext, BalancedSystem.subDemand, ht, htn]
  rw [h1, hA, hB, integral_sub (lci_int S _) hGI]
  ring
