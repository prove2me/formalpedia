-- Prove2me | solution 1 for SetCoverThreshold.MaxCover.prop_5_4
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:17:52.98993+00:00
-- url     : https://prove2.me/submissions/570166ce-7294-4dda-a10c-3122ea29ac2a

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_SetCoverThreshold_MaxCover_Formula
import Definitions.Def_SetCoverThreshold_MaxCover_ProofSystem
import Definitions.Def_SetCoverThreshold_MaxCover_Reduction

namespace SetCoverThreshold.MaxCover

open Classical in
theorem aux_p54_fib_card (φ : Formula5) {k ℓ : ℕ} (code : Fin k → Fin ℓ → Bool)
    (hcode : IsCode code) (i : Fin k) (r₀ : RandString φ ℓ) :
    (Finset.univ.filter (fun r : RandString φ ℓ =>
        question φ code r i = question φ code r₀ i)).card = 3 ^ (ℓ / 2) * 5 ^ (ℓ / 2) := by
  set q := question φ code r₀ i with hqdef
  have hset : Finset.univ.filter (fun r : RandString φ ℓ => question φ code r i = q) =
      Fintype.piFinset (fun j => Finset.univ.filter (fun y : Fin φ.M × Fin 3 =>
        (if code i j then Sum.inl y.1 else Sum.inr (φ.var y.1 y.2)) = q j)) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro h j; rw [← h]; rfl
    · intro h; funext j; exact h j
  rw [hset, Fintype.card_piFinset]
  have hA : ∀ j, (Finset.univ.filter (fun y : Fin φ.M × Fin 3 =>
        (if code i j then Sum.inl y.1 else Sum.inr (φ.var y.1 y.2)) = q j)).card =
        if code i j then 3 else 5 := by
    intro j
    by_cases hc : code i j = true
    · have hqj : q j = Sum.inl (r₀ j).1 := by simp [hqdef, question, hc]
      simp only [hc, if_true, hqj, Sum.inl.injEq]
      have : Finset.univ.filter (fun y : Fin φ.M × Fin 3 => y.1 = (r₀ j).1) =
          {(r₀ j).1} ×ˢ (Finset.univ : Finset (Fin 3)) := by
        ext y; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product,
          Finset.mem_singleton, and_true]
      rw [this, Finset.card_product]; simp
    · have hqj : q j = Sum.inr (φ.var (r₀ j).1 (r₀ j).2) := by simp [hqdef, question, hc]
      simp only [hc, hqj]
      simp only [Bool.false_eq_true, if_false, Sum.inr.injEq]
      set v := φ.var (r₀ j).1 (r₀ j).2
      set s := Finset.univ.filter (fun y : Fin φ.M × Fin 3 => φ.var y.1 y.2 = v)
      have hinj : Set.InjOn Prod.fst (s : Set (Fin φ.M × Fin 3)) := by
        intro y hy y' hy' hyy
        simp only [s, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hy hy'
        have h2 : y.2 = y'.2 := by
          apply φ.distinct_vars y.1
          show (φ.clause y.1 y.2).2 = (φ.clause y.1 y'.2).2
          have := hy.trans hy'.symm
          rw [hyy] at this ⊢
          simpa [Formula5.var, hyy] using this
        exact Prod.ext hyy h2
      rw [← Finset.card_image_of_injOn hinj]
      have himg : s.image Prod.fst =
          Finset.univ.filter (fun c => ∃ p, (φ.clause c p).2 = v) := by
        ext c
        simp only [s, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
          Prod.exists, exists_and_right, exists_eq_right]
        exact Iff.rfl
      rw [himg]
      exact φ.five v ⟨(r₀ j).1, (r₀ j).2, rfl⟩
  rw [Finset.prod_congr rfl (fun j _ => hA j), Finset.prod_ite, Finset.prod_const,
    Finset.prod_const]
  have h1 := hcode.1 i
  have h2 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin ℓ)))
    (fun j => code i j = true)
  rw [Finset.card_univ, Fintype.card_fin] at h2
  have e1 : (Finset.univ.filter (fun j => code i j = true)).card = ℓ / 2 := by omega
  have e2 : (Finset.univ.filter (fun j => ¬ code i j = true)).card = ℓ / 2 := by omega
  rw [e1, e2]

theorem aux_p54_sum_weight (φ : Formula5) {k ℓ : ℕ} (code : Fin k → Fin ℓ → Bool)
    (hcode : IsCode code) (C : Finset (SetIdx φ code)) (hC : C.card ≤ coverBudget φ code) :
    ∑ r, setWeight φ code C r ≤ k * Fintype.card (RandString φ ℓ) := by
  classical
  set F := 3 ^ (ℓ / 2) * 5 ^ (ℓ / 2) with hF
  have hfib : ∀ i (q : Question φ ℓ), q ∈ possibleQuestions φ code i →
      (Finset.univ.filter (fun r : RandString φ ℓ => question φ code r i = q)).card = F := by
    intro i q hq
    simp only [possibleQuestions, Finset.mem_image, Finset.mem_univ, true_and] at hq
    obtain ⟨r₀, rfl⟩ := hq
    convert aux_p54_fib_card φ code hcode i r₀
  have hR : ∀ i, Fintype.card (RandString φ ℓ) = (possibleQuestions φ code i).card * F := by
    intro i
    rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise
      (f := fun r => question φ code r i) (t := possibleQuestions φ code i)]
    · rw [Finset.sum_congr rfl (fun q hq => hfib i q hq), Finset.sum_const, smul_eq_mul]
    · intro r _; simp [possibleQuestions]
  have h1 : ∑ r, setWeight φ code C r = C.card * F := by
    have : ∀ r, setWeight φ code C r = ∑ s ∈ C, if s.2.1.1 = question φ code r s.1 then 1 else 0 := by
      intro r; rw [setWeight, Finset.card_filter]
    simp only [this]
    rw [Finset.sum_comm, Finset.card_eq_sum_ones C, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro s hs
    rw [one_mul, ← Finset.card_filter, ← hfib s.1 s.2.1.1 s.2.1.2]
    congr 1
    ext r; simp [eq_comm]
  calc ∑ r, setWeight φ code C r = C.card * F := h1
    _ ≤ coverBudget φ code * F := Nat.mul_le_mul_right _ hC
    _ = ∑ i : Fin k, Fintype.card (RandString φ ℓ) := by
        rw [coverBudget, Finset.sum_mul]; exact Finset.sum_congr rfl (fun i _ => (hR i).symm)
    _ = k * Fintype.card (RandString φ ℓ) := by simp

open Classical in
theorem aux_p54_fiber_bound (φ : Formula5) {k ℓ : ℕ} (code : Fin k → Fin ℓ → Bool) (hk : 1 ≤ k)
    (C : Finset (SetIdx φ code)) (r : RandString φ ℓ)
    (hcol : ¬ ∃ s ∈ C, ∃ s' ∈ C, s.1 ≠ s'.1 ∧ s.2.1.1 = question φ code r s.1 ∧
      s'.2.1.1 = question φ code r s'.1 ∧
      answerBits (fun j => (r j).2) s.2.2 = answerBits (fun j => (r j).2) s'.2.2) :
    (Fintype.card ((Fin ℓ → Bool) → Fin k) : ℝ) * (1 - 1 / (k:ℝ)) ^ (setWeight φ code C r) ≤
      (Fintype.card ((Fin ℓ → Bool) → Fin k) : ℝ) -
      ((Finset.univ.filter (fun x : (Fin ℓ → Bool) → Fin k => ∃ s ∈ C,
          s.2.1.1 = question φ code r s.1 ∧
          x (answerBits (fun j => (r j).2) s.2.2) = s.1)).card : ℝ) := by
  set lab : SetIdx φ code → (Fin ℓ → Bool) := fun s => answerBits (fun j => (r j).2) s.2.2
    with hlab
  set P := C.filter (fun s => s.2.1.1 = question φ code r s.1) with hP
  have hw : setWeight φ code C r = P.card := rfl
  set T : (Fin ℓ → Bool) → Finset (Fin k) :=
    fun L => Finset.univ.filter (fun i => ∀ s ∈ P, lab s = L → i ≠ s.1) with hT
  set n : (Fin ℓ → Bool) → ℕ := fun L => (P.filter (fun s => lab s = L)).card with hn
  have hsum : ∑ L, n L = P.card :=
    (Finset.card_eq_sum_card_fiberwise (f := lab) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)).symm
  have hkpos : (0:ℝ) < k := by exact_mod_cast hk
  have ha0 : 0 ≤ 1 - 1 / (k:ℝ) := by
    rw [sub_nonneg, div_le_one hkpos]; exact_mod_cast hk
  have ha1 : 1 - 1 / (k:ℝ) ≤ 1 := by
    have : 0 ≤ 1 / (k:ℝ) := by positivity
    linarith
  have hTL : ∀ L, (k:ℝ) * (1 - 1 / (k:ℝ)) ^ (n L) ≤ ((T L).card : ℝ) := by
    intro L
    by_cases h0 : n L = 0
    · have hTu : T L = Finset.univ := by
        ext i
        simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
        intro s hs hsL
        exfalso
        have hmem : s ∈ P.filter (fun s => lab s = L) := Finset.mem_filter.mpr ⟨hs, hsL⟩
        have : (P.filter (fun s => lab s = L)).card = 0 := h0
        rw [Finset.card_eq_zero] at this
        rw [this] at hmem
        exact absurd hmem (Finset.notMem_empty _)
      rw [h0, hTu]; simp
    · obtain ⟨s₀, hs₀⟩ : (P.filter (fun s => lab s = L)).Nonempty :=
        Finset.card_pos.mp (Nat.pos_of_ne_zero h0)
      rw [Finset.mem_filter] at hs₀
      have hsub : Finset.univ.erase s₀.1 ⊆ T L := by
        intro i hi
        rw [Finset.mem_erase] at hi
        simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and]
        intro s hs hsL hEq
        apply hcol
        refine ⟨s, (Finset.mem_filter.mp hs).1, s₀, (Finset.mem_filter.mp hs₀.1).1, ?_,
          (Finset.mem_filter.mp hs).2, (Finset.mem_filter.mp hs₀.1).2, ?_⟩
        · rw [← hEq]; exact hi.1
        · have e1 : lab s = L := hsL
          have e2 : lab s₀ = L := hs₀.2
          exact e1.trans e2.symm
      have hcard : (k:ℝ) - 1 ≤ (T L).card := by
        have h := Finset.card_le_card hsub
        rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
          Fintype.card_fin] at h
        have h' : ((k - 1 : ℕ) : ℝ) ≤ (T L).card := by exact_mod_cast h
        rw [Nat.cast_sub hk] at h'; simpa using h'
      have hpow : (1 - 1 / (k:ℝ)) ^ (n L) ≤ 1 - 1 / (k:ℝ) := pow_le_of_le_one ha0 ha1 h0
      calc (k:ℝ) * (1 - 1 / (k:ℝ)) ^ (n L) ≤ k * (1 - 1 / (k:ℝ)) :=
            mul_le_mul_of_nonneg_left hpow hkpos.le
        _ = k - 1 := by field_simp
        _ ≤ _ := hcard
  have hpi : Fintype.piFinset T ⊆ Finset.univ.filter (fun x : (Fin ℓ → Bool) → Fin k =>
      ¬ ∃ s ∈ C, s.2.1.1 = question φ code r s.1 ∧ x (lab s) = s.1) := by
    intro x hx
    rw [Fintype.mem_piFinset] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_exists, not_and]
    intro s hs hq hx'
    have := hx (lab s)
    simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and] at this
    exact this s (Finset.mem_filter.mpr ⟨hs, hq⟩) rfl hx'
  have hadd := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (fun x : (Fin ℓ → Bool) → Fin k => ∃ s ∈ C, s.2.1.1 = question φ code r s.1 ∧
      x (lab s) = s.1)
  have hK : (Fintype.card ((Fin ℓ → Bool) → Fin k) : ℝ) = ∏ _L : Fin ℓ → Bool, (k:ℝ) := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin]; push_cast; ring
  have hprod : (Fintype.card ((Fin ℓ → Bool) → Fin k) : ℝ) * (1 - 1 / (k:ℝ)) ^ P.card =
      ∏ L, ((k:ℝ) * (1 - 1 / (k:ℝ)) ^ (n L)) := by
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hsum, hK]
  rw [hw, hprod]
  calc ∏ L, ((k:ℝ) * (1 - 1 / (k:ℝ)) ^ (n L)) ≤ ∏ L, ((T L).card : ℝ) :=
        Finset.prod_le_prod (fun L _ => mul_nonneg hkpos.le (pow_nonneg ha0 _))
          (fun L _ => hTL L)
    _ = ((Fintype.piFinset T).card : ℝ) := by rw [Fintype.card_piFinset]; push_cast; rfl
    _ ≤ ((Finset.univ.filter (fun x : (Fin ℓ → Bool) → Fin k =>
      ¬ ∃ s ∈ C, s.2.1.1 = question φ code r s.1 ∧ x (lab s) = s.1)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hpi
    _ = _ := by
        show _ = _ - ((Finset.univ.filter (fun x : (Fin ℓ → Bool) → Fin k => ∃ s ∈ C,
          s.2.1.1 = question φ code r s.1 ∧ x (lab s) = s.1)).card : ℝ)
        rw [Finset.card_univ] at hadd
        rw [← hadd]; push_cast; ring

theorem aux_p54_tangent (a : ℝ) (ha : 0 < a) (w k : ℕ) :
    a ^ k + a ^ k * Real.log a * ((w:ℝ) - k) ≤ a ^ w := by
  have hw : a ^ w = Real.exp (w * Real.log a) := by rw [Real.exp_nat_mul, Real.exp_log ha]
  have hk : a ^ k = Real.exp (k * Real.log a) := by rw [Real.exp_nat_mul, Real.exp_log ha]
  have hsplit : Real.exp (w * Real.log a) =
      Real.exp (k * Real.log a) * Real.exp (((w:ℝ) - k) * Real.log a) := by
    rw [← Real.exp_add]; ring_nf
  have h1 := Real.add_one_le_exp (((w:ℝ) - k) * Real.log a)
  have hpos := Real.exp_pos (k * Real.log a)
  rw [hw, hsplit, hk]
  nlinarith

theorem aux_p54_limit (ε : ℝ) (hε : 0 < ε) : ∃ k₁ : ℕ, ∀ k : ℕ, k₁ ≤ k →
    Real.exp (-1) - ε / 3 < (1 - 1 / (k:ℝ)) ^ k := by
  have h := Real.tendsto_one_add_div_pow_exp (-1)
  have h2 := h.eventually (lt_mem_nhds (show Real.exp (-1) - ε / 3 < Real.exp (-1) by linarith))
  rw [Filter.eventually_atTop] at h2
  obtain ⟨N, hN⟩ := h2
  refine ⟨N, fun k hk => ?_⟩
  have := hN k hk
  simpa [sub_eq_add_neg, neg_div] using this

end SetCoverThreshold.MaxCover

open SetCoverThreshold.MaxCover

theorem solution (ε : ℝ) (hε : 0 < ε) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∀ (ℓ : ℕ) (code : Fin k → Fin ℓ → Bool), IsCode code →
      ∀ (φ : Formula5) (C : Finset (SetIdx φ code)), C.card ≤ coverBudget φ code →
        (1 - Real.exp (-1) + ε) *
            (Fintype.card (RandString φ ℓ × ((Fin ℓ → Bool) → Fin k)) : ℝ) ≤
          ((coveredMaxCover φ code C).card : ℝ) →
        ε / 3 * (Fintype.card (RandString φ ℓ) : ℝ) ≤ (goodCount φ code ε C : ℝ) := by
  classical
  obtain ⟨k₁, hk₁⟩ := aux_p54_limit ε hε
  refine ⟨max k₁ 2, ?_⟩
  intro k hk ℓ code hcode φ C hC hcov
  have hk1 : k₁ ≤ k := le_trans (le_max_left _ _) hk
  have hk2 : 2 ≤ k := le_trans (le_max_right _ _) hk
  have hkpos : (0:ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  set a : ℝ := 1 - 1 / (k:ℝ) with ha
  have ha0 : 0 < a := by
    rw [ha, sub_pos, div_lt_one hkpos]; exact_mod_cast (by omega : 1 < k)
  have ha1 : a ≤ 1 := by
    have : 0 ≤ 1 / (k:ℝ) := by positivity
    linarith
  have hlog : Real.log a ≤ 0 := Real.log_nonpos ha0.le ha1
  set R := Fintype.card (RandString φ ℓ) with hR
  set K := Fintype.card ((Fin ℓ → Bool) → Fin k) with hK
  have : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
  have hKpos : (0:ℝ) < K := by
    rw [hK]; exact_mod_cast Fintype.card_pos
  set w : RandString φ ℓ → ℕ := fun r => setWeight φ code C r with hw
  set Col : RandString φ ℓ → Prop := fun r => ∃ s ∈ C, ∃ s' ∈ C, s.1 ≠ s'.1 ∧
      s.2.1.1 = question φ code r s.1 ∧ s'.2.1.1 = question φ code r s'.1 ∧
      answerBits (fun j => (r j).2) s.2.2 = answerBits (fun j => (r j).2) s'.2.2 with hCol
  set Fr : RandString φ ℓ → Finset ((Fin ℓ → Bool) → Fin k) := fun r =>
    Finset.univ.filter (fun x : (Fin ℓ → Bool) → Fin k => ∃ s ∈ C,
          s.2.1.1 = question φ code r s.1 ∧
          x (answerBits (fun j => (r j).2) s.2.2) = s.1) with hFr
  -- Step 1: the covered points, counted copy by copy
  have hcovcard : (coveredMaxCover φ code C).card = ∑ r, (Fr r).card := by
    have : coveredMaxCover φ code C = Finset.univ.filter
        (fun p : RandString φ ℓ × ((Fin ℓ → Bool) → Fin k) => p.2 ∈ Fr p.1) := by
      ext p
      simp [coveredMaxCover, reductionSet, cubeSystem, hFr, eq_comm]
    rw [this, Finset.card_filter, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro r _
    simp
  -- Step 2: bound in each copy
  have hstep2 : ∀ r, ((Fr r).card : ℝ) ≤ (if Col r then (K:ℝ) else 0) + K * (1 - a ^ (w r)) := by
    intro r
    have hpow : a ^ (w r) ≤ 1 := pow_le_one₀ ha0.le ha1
    by_cases hc : Col r
    · rw [if_pos hc]
      have h1 : ((Fr r).card : ℝ) ≤ K := by
        rw [hK]; exact_mod_cast Finset.card_le_univ _
      have h2 : 0 ≤ (K:ℝ) * (1 - a ^ (w r)) := mul_nonneg hKpos.le (by linarith)
      linarith
    · rw [if_neg hc]
      have := aux_p54_fiber_bound φ code (by omega) C r hc
      linarith
  -- Step 3: averaging the coverage bound
  have hsw : ((∑ r, w r : ℕ) : ℝ) ≤ k * R := by
    exact_mod_cast aux_p54_sum_weight φ code hcode C hC
  have hstep3 : ∑ r, (1 - a ^ (w r)) ≤ (R:ℝ) * (1 - a ^ k) := by
    have ht : ∀ r, 1 - a ^ (w r) ≤ (1 - a ^ k) - a ^ k * Real.log a * ((w r : ℝ) - k) := by
      intro r; have := aux_p54_tangent a ha0 (w r) k; linarith
    have hsum_eq : ∑ r, ((1 - a ^ k) - a ^ k * Real.log a * ((w r : ℝ) - k)) =
        R * (1 - a ^ k) - a ^ k * Real.log a * ((∑ r, (w r : ℝ)) - k * R) := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib]
      simp [hR]
      ring
    have h1 : (∑ r, (w r : ℝ)) - k * R ≤ 0 := by push_cast at hsw; linarith
    have h2 : a ^ k * Real.log a ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (pow_nonneg ha0.le _) hlog
    calc ∑ r, (1 - a ^ (w r)) ≤ ∑ r, ((1 - a ^ k) - a ^ k * Real.log a * ((w r : ℝ) - k)) :=
          Finset.sum_le_sum (fun r _ => ht r)
      _ = _ := hsum_eq
      _ ≤ R * (1 - a ^ k) := by
          have : 0 ≤ (a ^ k * Real.log a) * ((∑ r, (w r : ℝ)) - k * R) :=
            mul_nonneg_of_nonpos_of_nonpos h2 h1
          linarith
  -- Step 4: collisions are good or heavy
  set B1 := Finset.univ.filter (fun r => (3 * k / ε : ℝ) < w r) with hB1
  have hstep4 : (Finset.univ.filter Col).card ≤ goodCount φ code ε C + B1.card := by
    have hsub : Finset.univ.filter Col ⊆ Finset.univ.filter (IsGood φ code ε C) ∪ B1 := by
      intro r hr
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
      rw [Finset.mem_union]
      by_cases hb : (3 * k / ε : ℝ) < w r
      · right; simp [hB1, hb]
      · left
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨le_of_not_gt hb, ?_⟩
        obtain ⟨s, hs, s', hs', h1, h2, h3, h4⟩ := hr
        exact ⟨s, hs, s', hs', h1, h2, h3, h4⟩
    calc _ ≤ _ := Finset.card_le_card hsub
      _ ≤ _ := Finset.card_union_le _ _
      _ = _ := by rw [goodCount]
  -- Step 5: Markov
  have hstep5 : (B1.card : ℝ) * (3 * k / ε) ≤ k * R := by
    calc (B1.card : ℝ) * (3 * k / ε) = ∑ r ∈ B1, (3 * k / ε : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ r ∈ B1, (w r : ℝ) :=
          Finset.sum_le_sum (fun r hr => le_of_lt (Finset.mem_filter.mp hr).2)
      _ ≤ ∑ r, (w r : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun _ _ _ => Nat.cast_nonneg _)
      _ ≤ k * R := by push_cast at hsw; exact hsw
  have hB1le : (B1.card : ℝ) ≤ ε * R / 3 := by
    have hpos : 0 < ε / (3 * k) := by positivity
    have := mul_le_mul_of_nonneg_right hstep5 hpos.le
    have e1 : (B1.card : ℝ) * (3 * k / ε) * (ε / (3 * k)) = B1.card := by field_simp
    have e2 : (k:ℝ) * R * (ε / (3 * k)) = ε * R / 3 := by field_simp
    linarith
  -- Step 6: the limit
  have hstep6 : 1 - a ^ k ≤ 1 - Real.exp (-1) + ε / 3 := by
    have := hk₁ k hk1; linarith
  -- Combine
  have hcov' : (K:ℝ) * ((1 - Real.exp (-1) + ε) * R) ≤ ∑ r, ((Fr r).card : ℝ) := by
    have : (Fintype.card (RandString φ ℓ × ((Fin ℓ → Bool) → Fin k)) : ℝ) = R * K := by
      rw [Fintype.card_prod]; push_cast; rfl
    rw [this, hcovcard] at hcov
    push_cast at hcov
    linarith
  have hsum2 : ∑ r, ((Fr r).card : ℝ) ≤
      (Finset.univ.filter Col).card * K + K * ∑ r, (1 - a ^ (w r)) := by
    calc ∑ r, ((Fr r).card : ℝ) ≤ ∑ r, ((if Col r then (K:ℝ) else 0) + K * (1 - a ^ (w r))) :=
          Finset.sum_le_sum (fun r _ => hstep2 r)
      _ = _ := by
          rw [Finset.sum_add_distrib, Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero,
            ← Finset.mul_sum, nsmul_eq_mul, add_zero]
  have hmain : (K:ℝ) * ((1 - Real.exp (-1) + ε) * R) ≤
      K * ((goodCount φ code ε C : ℝ) + B1.card + R * (1 - a ^ k)) := by
    have h4 : ((Finset.univ.filter Col).card : ℝ) ≤ goodCount φ code ε C + B1.card := by
      exact_mod_cast hstep4
    have h4' := mul_le_mul_of_nonneg_right h4 hKpos.le
    have h3' := mul_le_mul_of_nonneg_left hstep3 hKpos.le
    calc (K:ℝ) * ((1 - Real.exp (-1) + ε) * R) ≤ ∑ r, ((Fr r).card : ℝ) := hcov'
      _ ≤ _ := hsum2
      _ ≤ _ := add_le_add h4' h3'
      _ = _ := by ring
  have hfin := le_of_mul_le_mul_left hmain hKpos
  have hR0 : (0:ℝ) ≤ R := Nat.cast_nonneg _
  have h6' : (R:ℝ) * (1 - a ^ k) ≤ R * (1 - Real.exp (-1) + ε / 3) :=
    mul_le_mul_of_nonneg_left hstep6 hR0
  linarith
