-- Prove2me | solution 1 for RankingQueryCost.Joint.lemma_4_10
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T01:29:55.001782+00:00
-- url     : https://prove2.me/submissions/35d6cd98-5f9c-4b10-852b-bb1d5c7fe37a

import Definitions.Def_RankingQueryCost_Joint_Interaction

set_option autoImplicit false

namespace RQCLemma410
open RankingQueryCost.Joint

variable {n : ℕ}

/-- The degree of `i` in a set of pairs. -/
def deg (G : Finset (Pair n)) (i : Fin n) : ℕ := (G.filter fun e => e.1.1 = i ∨ e.1.2 = i).card

theorem sum_deg_le (G : Finset (Pair n)) : ∑ i, deg G i ≤ 2 * G.card := by
  have h1 : ∀ i, deg G i ≤ (G.filter fun e => e.1.1 = i).card + (G.filter fun e => e.1.2 = i).card := by
    intro i
    unfold deg
    rw [Finset.filter_or]
    exact Finset.card_union_le _ _
  calc ∑ i, deg G i ≤ ∑ i, ((G.filter fun e => e.1.1 = i).card + (G.filter fun e => e.1.2 = i).card) :=
        Finset.sum_le_sum fun i _ => h1 i
    _ = G.card + G.card := by
        rw [Finset.sum_add_distrib, ← Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_univ _),
          ← Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_univ _)]
    _ = 2 * G.card := by ring

/-- Move the set `M` to the top ranks, keeping the order of the complement. -/
def moveFun (M : Finset (Fin n)) (i : Fin n) : ℕ :=
  if i ∈ M then n - M.card + (M.filter fun j => j < i).card
  else (Mᶜ.filter fun j => j < i).card

theorem moveFun_lt (M : Finset (Fin n)) (i : Fin n) : moveFun M i < n := by
  unfold moveFun
  split_ifs with hi
  · have : (M.filter fun j => j < i).card < M.card :=
      Finset.card_lt_card ⟨Finset.filter_subset _ _, fun h =>
        lt_irrefl i (Finset.mem_filter.1 (h hi)).2⟩
    have hM : M.card ≤ n := by simpa using Finset.card_le_univ M
    omega
  · have : (Mᶜ.filter fun j => j < i).card < Mᶜ.card :=
      Finset.card_lt_card ⟨Finset.filter_subset _ _, fun h =>
        lt_irrefl i (Finset.mem_filter.1 (h (Finset.mem_compl.2 hi))).2⟩
    have : Mᶜ.card ≤ n := by simpa using Finset.card_le_univ Mᶜ
    omega

theorem moveFun_compl_lt (M : Finset (Fin n)) (i : Fin n) (hi : i ∉ M) : moveFun M i < n - M.card := by
  unfold moveFun
  rw [if_neg hi]
  have : (Mᶜ.filter fun j => j < i).card < Mᶜ.card :=
    Finset.card_lt_card ⟨Finset.filter_subset _ _, fun h =>
        lt_irrefl i (Finset.mem_filter.1 (h (Finset.mem_compl.2 hi))).2⟩
  rw [Finset.card_compl, Fintype.card_fin] at this
  exact this

theorem moveFun_mono_in (M : Finset (Fin n)) (i j : Fin n) (hi : i ∈ M) (hj : j ∈ M) (hij : i < j) :
    moveFun M i < moveFun M j := by
  unfold moveFun
  rw [if_pos hi, if_pos hj]
  have : (M.filter fun k => k < i).card < (M.filter fun k => k < j).card := by
    apply Finset.card_lt_card
    refine ⟨fun k hk => ?_, fun h => ?_⟩
    · simp only [Finset.mem_filter] at hk ⊢; exact ⟨hk.1, lt_trans hk.2 hij⟩
    · have := h (Finset.mem_filter.2 ⟨hi, hij⟩); simp at this
  omega

theorem moveFun_mono_out (M : Finset (Fin n)) (i j : Fin n) (hi : i ∉ M) (hj : j ∉ M) (hij : i < j) :
    moveFun M i < moveFun M j := by
  unfold moveFun
  rw [if_neg hi, if_neg hj]
  apply Finset.card_lt_card
  refine ⟨fun k hk => ?_, fun h => ?_⟩
  · simp only [Finset.mem_filter] at hk ⊢; exact ⟨hk.1, lt_trans hk.2 hij⟩
  · have := h (Finset.mem_filter.2 ⟨by simpa using hi, hij⟩); simp at this

theorem moveFun_ge (M : Finset (Fin n)) (i : Fin n) (hi : i ∈ M) : n - M.card ≤ moveFun M i := by
  unfold moveFun; rw [if_pos hi]; omega

theorem moveFun_injective (M : Finset (Fin n)) : Function.Injective (moveFun M) := by
  intro i j hij
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · by_cases hi : i ∈ M <;> by_cases hj : j ∈ M
    · exact absurd hij (moveFun_mono_in M i j hi hj h).ne
    · have := moveFun_ge M i hi; have := moveFun_compl_lt M j hj; omega
    · have := moveFun_ge M j hj; have := moveFun_compl_lt M i hi; omega
    · exact absurd hij (moveFun_mono_out M i j hi hj h).ne
  · by_cases hi : i ∈ M <;> by_cases hj : j ∈ M
    · exact absurd hij (moveFun_mono_in M j i hj hi h).ne'
    · have := moveFun_ge M i hi; have := moveFun_compl_lt M j hj; omega
    · have := moveFun_ge M j hj; have := moveFun_compl_lt M i hi; omega
    · exact absurd hij (moveFun_mono_out M j i hj hi h).ne'

def moveFin (M : Finset (Fin n)) (i : Fin n) : Fin n := ⟨moveFun M i, moveFun_lt M i⟩

theorem moveFin_injective (M : Finset (Fin n)) : Function.Injective (moveFin M) := by
  intro i j h
  exact moveFun_injective M (congrArg Fin.val h)

noncomputable def movePerm (M : Finset (Fin n)) : Rank n :=
  Equiv.ofBijective (moveFin M) (Finite.injective_iff_bijective.mp (moveFin_injective M))

theorem movePerm_apply (M : Finset (Fin n)) (i : Fin n) : ((movePerm M i : Fin n) : ℕ) = moveFun M i := rfl

/-- Pairs whose orientation changes under `movePerm M` have their lower endpoint in `M`. -/
theorem flip_lower_mem (M : Finset (Fin n)) (e : Pair n)
    (h : truthful (movePerm M) e ≠ truthful (Equiv.refl _) e) : e.1.1 ∈ M := by
  by_contra hM
  apply h
  have he : e.1.1 < e.1.2 := e.2
  have h1 : truthful (Equiv.refl (Fin n)) e = true := by simp [truthful, he]
  rw [h1]
  simp only [truthful, decide_eq_true_eq]
  show moveFin M e.1.1 < moveFin M e.1.2
  show moveFun M e.1.1 < moveFun M e.1.2
  by_cases h2 : e.1.2 ∈ M
  · have := moveFun_ge M e.1.2 h2; have := moveFun_compl_lt M e.1.1 hM; omega
  · exact moveFun_mono_out M _ _ hM h2 he


theorem disagreements_le (T : Transcript n) (M : Finset (Fin n))
    (htrue : ∀ e ∈ acquired T, T e = some (truthful (Equiv.refl _) e)) :
    disagreements T (movePerm M) ≤ ∑ i ∈ M, deg (acquired T) i := by
  unfold disagreements
  have h1 : ((acquired T).filter fun e => T e ≠ some (truthful (movePerm M) e)) ⊆
      (acquired T).filter fun e => e.1.1 ∈ M := by
    intro e he
    rw [Finset.mem_filter] at he ⊢
    refine ⟨he.1, flip_lower_mem M e ?_⟩
    intro heq
    apply he.2
    rw [htrue e he.1, heq]
  refine le_trans (Finset.card_le_card h1) ?_
  have h2 := Finset.card_eq_sum_card_fiberwise (s := (acquired T).filter fun e => e.1.1 ∈ M)
    (t := M) (f := fun e : Pair n => e.1.1) (fun e he => (Finset.mem_filter.1 he).2)
  rw [h2]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.card_le_card
  intro e he
  simp only [Finset.mem_filter] at he ⊢
  exact ⟨he.1.1, Or.inl he.2⟩

theorem sqErr_triangle (x y z : Fin n → ℝ) :
    squaredError x z ≤ 2 * squaredError x y + 2 * squaredError y z := by
  unfold squaredError
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  nlinarith [sq_nonneg (x i + z i - 2 * y i)]

theorem core (n s B : ℕ) (τ : ℝ) (hn16 : 16 ≤ n) (h4 : 4 ∣ n) (hτ : 0 < τ)
    (hτc : τ ≤ 1 / 1024) (T : Transcript n) (hB : (acquired T).card ≤ B)
    (htrue : ∀ e ∈ acquired T, T e = some (truthful (Equiv.refl _) e)) (q : Fin n → ℝ)
    (hsound : ∀ r ∈ compatible s T, loss q r ≤ τ) :
    (1 / 1024 : ℝ) * min ((n : ℝ) * s) ((s : ℝ) / τ) ≤ B := by
  by_contra hlt
  push Not at hlt
  have hnR : (16 : ℝ) ≤ n := by exact_mod_cast hn16
  have hnpos : (0 : ℝ) < n := by linarith
  set G := acquired T with hG
  set F : Finset (Fin n) := Finset.univ.filter fun i => i.val < n / 4 with hF
  have hFcard : F.card = n / 4 := by
    rw [hF, Fin.card_filter_val_lt]; omega
  set L : Finset (Fin n) := F.filter fun i => n * deg G i ≤ 16 * B with hL
  have hFL : 8 * (F.filter fun i => ¬ (n * deg G i ≤ 16 * B)).card ≤ n := by
    set D := F.filter fun i => ¬ (n * deg G i ≤ 16 * B)
    have hsum : ∑ i ∈ D, n * deg G i ≤ 2 * n * B := by
      calc ∑ i ∈ D, n * deg G i ≤ ∑ i, n * deg G i :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => Nat.zero_le _)
        _ = n * ∑ i, deg G i := by rw [Finset.mul_sum]
        _ ≤ n * (2 * G.card) := Nat.mul_le_mul_left _ (sum_deg_le G)
        _ ≤ 2 * n * B := by nlinarith
    have hlow : D.card * (16 * B + 1) ≤ ∑ i ∈ D, n * deg G i := by
      have := Finset.card_nsmul_le_sum D (fun i => n * deg G i) (16 * B + 1) (by
        intro i hi
        have := (Finset.mem_filter.1 hi).2
        omega)
      simpa [smul_eq_mul] using this
    rcases Nat.eq_zero_or_pos B with hB0 | hBpos
    · subst hB0
      simp only [mul_zero, zero_add, mul_one] at hsum hlow
      omega
    · nlinarith
  have hLcard : n ≤ 8 * L.card := by
    have := Finset.card_filter_add_card_filter_not (s := F) (fun i => n * deg G i ≤ 16 * B)
    rw [hFcard] at this
    obtain ⟨k, hk⟩ := h4
    subst hk
    rw [← hL] at this
    omega
  set m := ⌈32 * (n : ℝ) * τ⌉₊ with hm
  have hm_lt : (m : ℝ) < 32 * n * τ + 1 := Nat.ceil_lt_add_one (by positivity)
  have hm_ge : 32 * (n : ℝ) * τ ≤ m := Nat.le_ceil _
  have h8m : 8 * m ≤ n := by
    have : (8 * m : ℝ) ≤ n := by nlinarith
    exact_mod_cast this
  obtain ⟨M, hML, hMcard⟩ := Finset.exists_subset_card_eq (s := L) (n := m) (by omega)
  -- disagreements
  have hdeg : n * ∑ i ∈ M, deg G i ≤ m * (16 * B) := by
    rw [Finset.mul_sum, ← hMcard]
    have := Finset.sum_le_card_nsmul M (fun i => n * deg G i) (16 * B) (by
      intro i hi
      exact (Finset.mem_filter.1 (hML hi)).2)
    simpa [smul_eq_mul] using this
  have hB1 : (B : ℝ) * (1024 * τ) < s := by
    have h := lt_of_lt_of_le hlt (mul_le_mul_of_nonneg_left (min_le_right ((n : ℝ) * s) ((s : ℝ) / τ))
      (by norm_num : (0 : ℝ) ≤ 1 / 1024))
    have : (1 / 1024 : ℝ) * ((s : ℝ) / τ) * (1024 * τ) = s := by field_simp
    nlinarith
  have hB2 : (B : ℝ) * 1024 < n * s := by
    have h := lt_of_lt_of_le hlt (mul_le_mul_of_nonneg_left (min_le_left ((n : ℝ) * s) ((s : ℝ) / τ))
      (by norm_num : (0 : ℝ) ≤ 1 / 1024))
    linarith
  have hdis : disagreements T (movePerm M) ≤ s := by
    have h1 := disagreements_le T M htrue
    have h2 : (n : ℝ) * ((∑ i ∈ M, deg G i : ℕ) : ℝ) ≤ m * (16 * B) := by exact_mod_cast hdeg
    have hB0 : (0 : ℝ) ≤ B := by positivity
    have h3 : (m : ℝ) * (16 * B) ≤ (32 * n * τ + 1) * (16 * B) :=
      mul_le_mul_of_nonneg_right hm_lt.le (by positivity)
    have h4' : (n : ℝ) * ((∑ i ∈ M, deg G i : ℕ) : ℝ) < n * s := by nlinarith
    have h5 : ((∑ i ∈ M, deg G i : ℕ) : ℝ) < s := lt_of_mul_lt_mul_left h4' hnpos.le
    have h6 : (∑ i ∈ M, deg G i) < s := by exact_mod_cast h5
    exact le_trans h1 (by rw [← hG]; omega)
  have hcompσ : movePerm M ∈ compatible s T := hdis
  have hcompId : (Equiv.refl (Fin n)) ∈ compatible s T := by
    show disagreements T (Equiv.refl (Fin n)) ≤ s
    have : disagreements T (Equiv.refl (Fin n)) = 0 := by
      unfold disagreements
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro e he hne
      exact hne (htrue e he)
    omega
  have hn3 : (0 : ℝ) < (n : ℝ) ^ 3 := by positivity
  have l1 := hsound _ hcompId
  have l2 := hsound _ hcompσ
  unfold loss at l1 l2
  rw [div_le_iff₀ hn3] at l1 l2
  have hsymm : squaredError (rankVector (Equiv.refl (Fin n))) q =
      squaredError q (rankVector (Equiv.refl (Fin n))) := by
    unfold squaredError; congr 1; ext i; ring
  have htri := sqErr_triangle (rankVector (Equiv.refl (Fin n))) q (rankVector (movePerm M))
  rw [hsymm] at htri
  -- lower bound on the displacement
  have hlow : (m : ℝ) * ((n : ℝ) ^ 2 / 4) ≤
      squaredError (rankVector (Equiv.refl (Fin n))) (rankVector (movePerm M)) := by
    unfold squaredError
    have hsub : ∑ i ∈ M, (rankVector (Equiv.refl (Fin n)) i - rankVector (movePerm M) i) ^ 2 ≤
        ∑ i, (rankVector (Equiv.refl (Fin n)) i - rankVector (movePerm M) i) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => sq_nonneg _)
    refine le_trans ?_ hsub
    rw [← hMcard]
    have := Finset.card_nsmul_le_sum M
      (fun i => (rankVector (Equiv.refl (Fin n)) i - rankVector (movePerm M) i) ^ 2)
      ((n : ℝ) ^ 2 / 4) (by
        intro i hi
        have hiF : i ∈ F := (Finset.mem_filter.1 (hML hi)).1
        have hi4 : i.val < n / 4 := (Finset.mem_filter.1 hiF).2
        have hσ := moveFun_ge M i hi
        rw [hMcard] at hσ
        have hi4R : ((i.val : ℕ) : ℝ) + 1 ≤ n / 4 := by
          obtain ⟨k, hk⟩ := h4
          subst hk
          have : i.val + 1 ≤ k := by omega
          have : ((i.val : ℕ) : ℝ) + 1 ≤ k := by exact_mod_cast this
          push_cast; linarith
        have hσR : (n : ℝ) - m ≤ (moveFun M i : ℝ) := by
          have : ((n - m : ℕ) : ℝ) ≤ (moveFun M i : ℝ) := by exact_mod_cast hσ
          rw [Nat.cast_sub (by omega)] at this; exact this
        have h8mR : (8 * m : ℝ) ≤ n := by exact_mod_cast h8m
        simp only [rankVector, Equiv.refl_apply]
        rw [movePerm_apply]
        nlinarith)
    simpa [smul_eq_mul] using this
  have : (m : ℝ) * ((n : ℝ) ^ 2 / 4) ≥ 8 * τ * (n : ℝ) ^ 3 := by
    have : (32 * (n : ℝ) * τ) * ((n : ℝ) ^ 2 / 4) ≤ m * ((n : ℝ) ^ 2 / 4) :=
      mul_le_mul_of_nonneg_right hm_ge (by positivity)
    nlinarith
  nlinarith

/-- The clean identity world. -/
def cleanWorld (n : ℕ) : ComparisonWorld n := ⟨Equiv.refl _, ∅, fun _ _ _ _ => (false, false)⟩

def TruthfulLedger (S : InteractionState n) : Prop :=
  ∀ e b, S.ledger e = some b → b = truthful (Equiv.refl _) e

theorem truthful_step (S : InteractionState n) (msg : List ℕ) (e : Pair n)
    (hS : TruthfulLedger S) : TruthfulLedger (readIdentity 0 (cleanWorld n) S msg e).2 := by
  unfold readIdentity
  cases hle : S.ledger e with
  | some b => simp only [hle]; exact hS
  | none =>
    intro f b hf
    simp only [cleanWorld, Finset.notMem_empty, false_or, not_false_eq_true, true_and,
      Bool.false_eq_true, false_and, if_false] at hf
    by_cases hfe : f = e
    · subst hfe; simp at hf; exact hf.symm
    · rw [Function.update_of_ne hfe] at hf; exact hS f b hf

theorem truthful_prefix (A : QueryPolicy n) (ω : PrivateTape) :
    ∀ t, TruthfulLedger (executionState (executionPrefix A (cleanWorld n) 0 ω t)) := by
  intro t
  induction t with
  | zero => intro e b h; simp [executionPrefix, executionState, initialState, emptyTranscript] at h
  | succ t ih =>
    simp only [executionPrefix]
    generalize executionPrefix A (cleanWorld n) 0 ω t = X at ih
    cases X with
    | running S =>
      simp only [advance]
      rcases A.request ω S.history with _ | _ | e
      · exact ih
      · exact ih
      · exact truthful_step _ _ _ ih
    | halted o => exact ih
    | diverged S => exact ih

end RQCLemma410

open RankingQueryCost.Joint RQCLemma410

theorem solution :
    ∃ c : ℝ, 0 < c ∧ ∀ (n s B : ℕ) (τ : ℝ),
      Admissible n s → 0 < τ → τ ≤ precisionCeiling →
      ∀ (A : QueryPolicy n) (V : PublicVerifier n),
        HardBudget s 0 B A → VerifierSound s τ V →
        (∀ W, LegalWorld s W → ∀ ω o, Returns A W 0 ω o → o.emission = true →
          o.estimate ∈ estimateSet n ∧ V o.state.ledger o.estimate o.certificate = true) →
        (∀ W : ComparisonWorld n, W.initial = ∅ →
          0 < privateLaw {ω | ∃ o, Returns A W 0 ω o ∧ o.emission = true}) →
        c * min ((n : ℝ) * s) ((s : ℝ) / τ) ≤ (B : ℝ) := by
  refine ⟨1 / 1024, by norm_num, ?_⟩
  intro n s B τ hadm hτ hτc A V hB hV hemit hpos
  have h0 := hpos (cleanWorld n) rfl
  obtain ⟨ω, o, hR, hem⟩ := MeasureTheory.nonempty_of_measure_ne_zero h0.ne'
  have hlegal : LegalWorld s (cleanWorld n) := by simp [LegalWorld, cleanWorld]
  obtain ⟨hq, hacc⟩ := hemit _ hlegal ω o hR hem
  have hsound := hV _ _ _ hq hacc
  obtain ⟨t, ht⟩ := hR
  have hBt := hB _ hlegal ω t
  have htr := truthful_prefix A ω t
  rw [ht] at hBt htr
  simp only [executionState] at hBt htr
  refine core n s B τ hadm.1 hadm.2.1 hτ (by simpa [precisionCeiling] using hτc)
    o.state.ledger hBt ?_ o.estimate hsound
  intro e he
  have hs : (o.state.ledger e).isSome = true := (Finset.mem_filter.1 he).2
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hs
  rw [hb, htr e b hb]
