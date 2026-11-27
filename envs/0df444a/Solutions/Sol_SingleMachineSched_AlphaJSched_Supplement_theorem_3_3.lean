-- Prove2me | solution 1 for SingleMachineSched.AlphaJSched.Supplement.theorem_3_3
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:26:06.886794+00:00
-- url     : https://prove2.me/submissions/e06e88d7-7ae2-4ec3-a555-ae825bc1c1c9

import Mathlib
import Definitions.Def_SingleMachineSched_AlphaJSched_AlphaJSchedule
import Definitions.Def_SingleMachineSched_Shared_RelaxationR
import Definitions.Def_SingleMachineSched_AlphaJSched_Supplement_Optima

open SingleMachineSched
open SingleMachineSched.AlphaJSched
open SingleMachineSched.AlphaJSched.Supplement

/-- Theorem 3.3: common α, its special factor at 1/√2, and the simultaneous makespan bound. -/
theorem solution {n : ℕ} (p r : Fin n → ℕ) (w : Fin n → ℝ)
    (hp : ∀ j, 0 < p j) (hw : ∀ j, 0 < w j)
    (hsort : ∀ j k : Fin n, j ≤ k → w k / p k ≤ w j / p j)
    (α : ℝ) (hα : 0 < α ∧ α ≤ 1) :
    (∑ j, w j * (alphaCompletion p r (fun _ => α) j : ℝ) ≤
      max (1 + 1 / α) (1 + 2 * α) * Shared.zR p r w) ∧
    (max (1 + 1 / (1 / Real.sqrt 2)) (1 + 2 * (1 / Real.sqrt 2)) =
      1 + Real.sqrt 2) ∧
    (∀ j, (alphaCompletion p r (fun _ => α) j : ℝ) ≤
      (1 + α) * optMakespan p r) := by
        classical
        have h2 : max (1 + 1 / (1 / Real.sqrt 2)) (1 + 2 * (1 / Real.sqrt 2)) =
            1 + Real.sqrt 2 := by
          have hs : (0:ℝ) < Real.sqrt 2 := by positivity
          have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
          have e1 : 1 + 1 / (1 / Real.sqrt 2) = 1 + Real.sqrt 2 := by
            rw [one_div_one_div]
          have e2 : 1 + 2 * (1 / Real.sqrt 2) = 1 + Real.sqrt 2 := by
            field_simp
            linarith
          rw [e1, e2, max_self]
        -- total length of a feasible nonpreemptive schedule within horizon T
        have hsumT : ∀ (s : Fin n → ℝ) (T : ℝ), IsNonpreemptiveSchedule p r s →
            (∀ j, s j + (p j : ℝ) ≤ T) → ∀ (t0 : ℝ) (S : Finset (Fin n)),
            (∀ i ∈ S, t0 ≤ (r i : ℝ)) → t0 + ∑ i ∈ S, (p i : ℝ) ≤ T ∨ S = ∅ := by
          intro s T hs hT t0 S hS
          by_cases hSe : S = ∅
          · exact Or.inr hSe
          left
          have hsub : (⋃ i ∈ S, Set.Ico (s i) (s i + p i)) ⊆ Set.Ico t0 T := by
            intro x hx
            simp only [Set.mem_iUnion, Set.mem_Ico] at hx
            obtain ⟨i, hi, h1, h2⟩ := hx
            exact ⟨le_trans (le_trans (hS i hi) (hs.1 i)) h1, lt_of_lt_of_le h2 (hT i)⟩
          have hdisj : (S : Set (Fin n)).PairwiseDisjoint (fun i => Set.Ico (s i) (s i + p i)) := by
            intro i _ k _ hik
            rcases hs.2 i k hik with h | h
            · exact Set.Ico_disjoint_Ico.mpr (le_trans (min_le_left _ _) (le_trans h (le_max_right _ _)))
            · exact Set.Ico_disjoint_Ico.mpr (le_trans (min_le_right _ _) (le_trans h (le_max_left _ _)))
          have hm := MeasureTheory.measure_biUnion_finset (μ := MeasureTheory.volume) hdisj
            (fun i _ => measurableSet_Ico)
          have hle := MeasureTheory.measure_mono (μ := MeasureTheory.volume) hsub
          rw [hm] at hle
          simp only [Real.volume_Ico] at hle
          have hT0 : t0 ≤ T := by
            obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hSe
            have := hT i; have := hs.1 i; have := hS i hi
            have : (0:ℝ) ≤ p i := by positivity
            linarith
          rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => by
            have : (0:ℝ) ≤ p i := by positivity
            linarith)] at hle
          rw [ENNReal.ofReal_le_ofReal_iff (by linarith)] at hle
          have : ∑ i ∈ S, (s i + p i - s i) = ∑ i ∈ S, (p i : ℝ) := by
            apply Finset.sum_congr rfl; intro i _; ring
          linarith
        have F4 : ∀ τ j, lpRemaining p r (τ+1) j =
            if lpRun p r τ = some j then lpRemaining p r τ j - 1 else lpRemaining p r τ j := by
          intro τ j; rfl
        have F2 : ∀ τ j, lpRun p r τ = some j → r j ≤ τ ∧ 0 < lpRemaining p r τ j := by
          intro τ j h
          unfold lpRun lpPick at h
          split_ifs at h with hne
          · have := Finset.min'_mem _ hne
            rw [Option.some_inj] at h
            rw [h] at this
            simpa using this
        have F3 : ∀ τ, lpRun p r τ = none → ∀ j, 0 < lpRemaining p r τ j → τ < r j := by
          intro τ h j hj
          unfold lpRun lpPick at h
          split_ifs at h with hne
          by_contra hc
          exact hne ⟨j, by simp; omega⟩
        have F1 : ∀ τ j, lpRemaining p r τ j ≤ p j := by
          intro τ j
          induction τ with
          | zero => rfl
          | succ τ ih => rw [F4]; split_ifs <;> omega
        have Fmono : ∀ τ j, lpRemaining p r (τ+1) j ≤ lpRemaining p r τ j := by
          intro τ j; rw [F4]; split_ifs <;> omega
        have Fmem : ∀ j (x : ℝ), x ∈ lpSet p r j ↔ 0 ≤ x ∧ lpRun p r ⌊x⌋₊ = some j := by
          intro j x
          unfold lpSet
          simp only [Set.mem_iUnion, Set.mem_Ico, exists_prop]
          constructor
          · rintro ⟨τ, h, h1, h2⟩
            have h0 : (0:ℝ) ≤ x := le_trans (Nat.cast_nonneg _) h1
            refine ⟨h0, ?_⟩
            rw [(Nat.floor_eq_iff h0).mpr ⟨h1, h2⟩]; exact h
          · rintro ⟨h0, h⟩
            exact ⟨⌊x⌋₊, h, Nat.floor_le h0, Nat.lt_floor_add_one x⟩
        have F6 : ∀ j (τ : ℕ), MeasureTheory.volume (lpSet p r j ∩ Set.Iio (τ:ℝ)) =
            ((p j - lpRemaining p r τ j : ℕ) : ENNReal) := by
          intro j τ
          induction τ with
          | zero =>
            have : lpSet p r j ∩ Set.Iio ((0:ℕ):ℝ) = ∅ := by
              ext x; simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_empty_iff_false, iff_false,
                not_and, Fmem]
              intro h; push_cast; linarith [h.1]
            rw [this]; simp [lpRemaining]
          | succ τ ih =>
            by_cases hr : lpRun p r τ = some j
            · have hset : lpSet p r j ∩ Set.Iio ((τ+1:ℕ):ℝ) =
                  (lpSet p r j ∩ Set.Iio (τ:ℝ)) ∪ Set.Ico (τ:ℝ) (τ+1) := by
                ext x
                simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_union, Set.mem_Ico]
                push_cast
                constructor
                · rintro ⟨hx, h1⟩
                  by_cases hxt : x < τ
                  · exact Or.inl ⟨hx, hxt⟩
                  · exact Or.inr ⟨le_of_not_gt hxt, h1⟩
                · rintro (⟨hx, h1⟩ | ⟨h1, h2⟩)
                  · exact ⟨hx, by linarith⟩
                  · refine ⟨?_, h2⟩
                    have h0 : (0:ℝ) ≤ x := le_trans (Nat.cast_nonneg _) h1
                    rw [Fmem]; refine ⟨h0, ?_⟩
                    rw [(Nat.floor_eq_iff h0).mpr ⟨h1, h2⟩]; exact hr
              rw [hset, MeasureTheory.measure_union _ measurableSet_Ico, ih, Real.volume_Ico]
              · have := F2 τ j hr
                have := F1 τ j
                rw [F4, if_pos hr]
                have e : (τ:ℝ) + 1 - τ = 1 := by ring
                rw [e, ENNReal.ofReal_one]
                rw [← Nat.cast_one (R := ENNReal), ← Nat.cast_add]
                congr 1; omega
              · rw [Set.disjoint_left]
                rintro x ⟨_, hx⟩ ⟨hx2, _⟩
                exact absurd hx (not_lt.mpr hx2)
            · have hset : lpSet p r j ∩ Set.Iio ((τ+1:ℕ):ℝ) = lpSet p r j ∩ Set.Iio (τ:ℝ) := by
                ext x
                simp only [Set.mem_inter_iff, Set.mem_Iio]
                push_cast
                constructor
                · rintro ⟨hx, h1⟩
                  refine ⟨hx, ?_⟩
                  by_contra hxt
                  rw [Fmem] at hx
                  rw [(Nat.floor_eq_iff hx.1).mpr ⟨le_of_not_gt hxt, h1⟩] at hx
                  exact hr hx.2
                · rintro ⟨hx, h1⟩; exact ⟨hx, by linarith⟩
              rw [hset, ih, F4, if_neg hr]
        have hfacts : ∀ (s : Fin n → ℝ) (T : ℝ), IsNonpreemptiveSchedule p r s →
            (∀ j, s j + (p j : ℝ) ≤ T) →
            (∀ τ : ℕ, ∑ j, (lpRemaining p r τ j : ℝ) ≤ max 0 (T - τ)) ∧
            (∃ τ0 : ℕ, ∀ σ j, τ0 ≤ σ → lpRemaining p r σ j = 0) ∧
            (∀ j, (r j : ℝ) ≤ alphaPoint p (lpSet p r) j α) ∧
            (∀ i (τ : ℕ), (τ:ℝ) ≤ alphaPoint p (lpSet p r) i α →
              ((p i - lpRemaining p r τ i : ℕ) : ℝ) ≤ α * p i) ∧
            (∀ i (τ : ℕ), alphaPoint p (lpSet p r) i α ≤ τ →
              α * p i ≤ ((p i - lpRemaining p r τ i : ℕ) : ℝ)) ∧
            (∀ j (b : ℕ), lpRemaining p r b j = 0 → alphaPoint p (lpSet p r) j α ≤ b) := by
          intro s T hs hsT
          have hsumT := hsumT s T hs hsT
          have F5 : ∀ τ : ℕ, ∑ j, (lpRemaining p r τ j : ℝ) ≤ max 0 (T - τ) := by
            intro τ
            induction τ with
            | zero =>
              rcases hsumT 0 Finset.univ (fun i _ => by positivity) with h | h
              · simp only [lpRemaining, Nat.cast_zero, sub_zero]; exact le_trans (by linarith) (le_max_right _ _)
              · simp [lpRemaining, h]
            | succ τ ih =>
              rcases hrun : lpRun p r τ with _ | j0
              · have he : ∀ j, lpRemaining p r (τ+1) j = lpRemaining p r τ j := by
                  intro j; rw [F4, hrun]; simp
                simp only [he]
                set S := Finset.univ.filter (fun j => τ + 1 ≤ r j)
                have hsub : ∑ j, (lpRemaining p r τ j : ℝ) = ∑ j ∈ S, (lpRemaining p r τ j : ℝ) := by
                  symm
                  apply Finset.sum_subset (Finset.subset_univ _)
                  intro j _ hj
                  simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hj
                  have : lpRemaining p r τ j = 0 := by
                    by_contra hc
                    have := F3 τ hrun j (Nat.pos_of_ne_zero hc); omega
                  simp [this]
                have hle : ∑ j ∈ S, (lpRemaining p r τ j : ℝ) ≤ ∑ j ∈ S, (p j : ℝ) :=
                  Finset.sum_le_sum (fun j _ => by exact_mod_cast F1 τ j)
                rcases hsumT ((τ+1:ℕ):ℝ) S (fun i hi => by
                  simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hi
                  exact_mod_cast hi) with h | h
                · rw [hsub]; exact le_trans (by linarith) (le_max_right _ _)
                · rw [hsub, h]; simp
              · have he : ∀ j, (lpRemaining p r (τ+1) j : ℝ) = lpRemaining p r τ j -
                    if j0 = j then 1 else 0 := by
                  intro j; rw [F4, hrun]
                  by_cases hj : j0 = j
                  · subst hj
                    have := (F2 τ j0 hrun).2
                    simp only [if_true]
                    rw [Nat.cast_sub (by omega)]; simp
                  · have : (some j0 = some j) = False := by simp [hj]
                    simp [hj]
                simp only [he]
                rw [Finset.sum_sub_distrib, Finset.sum_ite_eq]
                simp only [Finset.mem_univ, if_true]
                have h1 : (1:ℝ) ≤ ∑ j, (lpRemaining p r τ j : ℝ) := by
                  have := (F2 τ j0 hrun).2
                  have h' : (1:ℝ) ≤ lpRemaining p r τ j0 := by exact_mod_cast this
                  exact le_trans h' (Finset.single_le_sum (f := fun j => (lpRemaining p r τ j : ℝ))
                    (fun i _ => by positivity) (Finset.mem_univ j0))
                rcases le_total 0 (T - τ) with h | h
                · rw [max_eq_right h] at ih
                  push_cast
                  exact le_trans (by linarith) (le_max_right _ _)
                · rw [max_eq_left h] at ih; linarith
          obtain ⟨τ0, hτ0⟩ : ∃ τ0 : ℕ, ∀ j, lpRemaining p r τ0 j = 0 := by
            refine ⟨⌈T⌉₊, fun j => ?_⟩
            have h := F5 ⌈T⌉₊
            have hT : T - (⌈T⌉₊ : ℝ) ≤ 0 := by linarith [Nat.le_ceil T]
            rw [max_eq_left hT] at h
            have := Finset.single_le_sum (f := fun j => (lpRemaining p r ⌈T⌉₊ j : ℝ))
              (fun i _ => by positivity) (Finset.mem_univ j)
            have : (lpRemaining p r ⌈T⌉₊ j : ℝ) ≤ 0 := by linarith
            exact_mod_cast le_antisymm (by exact_mod_cast this) (Nat.zero_le _)
          have hzero : ∀ σ j, τ0 ≤ σ → lpRemaining p r σ j = 0 := by
            intro σ j h
            induction σ, h using Nat.le_induction with
            | base => exact hτ0 j
            | succ σ _ ih => have := Fmono σ j; omega
          have Gsub : ∀ j, lpSet p r j ⊆ Set.Iio (τ0:ℝ) := by
            intro j x hx
            rw [Fmem] at hx
            have h2 := (F2 _ j hx.2).2
            have : ⌊x⌋₊ < τ0 := by
              by_contra hc; have := hzero ⌊x⌋₊ j (by omega); omega
            have h3 := Nat.lt_floor_add_one x
            simp only [Set.mem_Iio]
            have h4 : ((⌊x⌋₊ + 1 : ℕ):ℝ) ≤ τ0 := by exact_mod_cast this
            push_cast at h4; linarith
          have Gfin : ∀ j (X : Set ℝ), MeasureTheory.volume (lpSet p r j ∩ X) ≠ ⊤ := by
            intro j X
            apply ne_top_of_le_ne_top (b := MeasureTheory.volume (lpSet p r j ∩ Set.Iio (τ0:ℝ)))
            · rw [F6]; exact ENNReal.natCast_ne_top _
            · apply MeasureTheory.measure_mono
              intro x hx; exact ⟨hx.1, Gsub j hx.1⟩
          have Gr : ∀ j (x : ℝ), x ∈ lpSet p r j → (r j : ℝ) ≤ x := by
            intro j x hx
            rw [Fmem] at hx
            have := (F2 _ j hx.2).1
            exact le_trans (by exact_mod_cast this) (Nat.floor_le hx.1)
          have Gb : ∀ j (t : ℝ), α * (p j : ℝ) ≤ (MeasureTheory.volume (lpSet p r j ∩ Set.Iic t)).toReal →
              (r j : ℝ) ≤ t := by
            intro j t ht
            by_contra hc
            have : lpSet p r j ∩ Set.Iic t = ∅ := by
              ext x; simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_empty_iff_false, iff_false, not_and]
              intro hx hxt; have := Gr j x hx; linarith
            rw [this] at ht; simp at ht
            have : (0:ℝ) < p j := by exact_mod_cast hp j
            nlinarith [hα.1]
          have G2 : ∀ j, (r j : ℝ) ≤ alphaPoint p (lpSet p r) j α := by
            intro j
            apply le_csInf
            · refine ⟨τ0, ?_⟩
              show α * (p j : ℝ) ≤ (MeasureTheory.volume (lpSet p r j ∩ Set.Iic (τ0:ℝ))).toReal
              have h1 : (MeasureTheory.volume (lpSet p r j ∩ Set.Iio (τ0:ℝ))).toReal ≤
                  (MeasureTheory.volume (lpSet p r j ∩ Set.Iic (τ0:ℝ))).toReal :=
                ENNReal.toReal_mono (Gfin j _) (MeasureTheory.measure_mono
                  (Set.inter_subset_inter_right _ Set.Iio_subset_Iic_self))
              rw [F6, hτ0] at h1
              simp only [Nat.sub_zero, ENNReal.toReal_natCast] at h1
              have : (0:ℝ) ≤ p j := by positivity
              nlinarith [hα.2]
            · intro t ht; exact Gb j t ht
          have G3 : ∀ i (τ : ℕ), (τ:ℝ) ≤ alphaPoint p (lpSet p r) i α →
              ((p i - lpRemaining p r τ i : ℕ) : ℝ) ≤ α * p i := by
            intro i τ hτ
            by_contra hc
            push Not at hc
            set d : ℝ := ((p i - lpRemaining p r τ i : ℕ) : ℝ)
            set ε := d - α * p i with hε
            have hεpos : 0 < ε := by linarith
            have hsub : lpSet p r i ∩ Set.Iio (τ:ℝ) ⊆
                (lpSet p r i ∩ Set.Iic ((τ:ℝ) - ε)) ∪ Set.Ioo ((τ:ℝ) - ε) τ := by
              intro x ⟨hx, hx2⟩
              by_cases h : x ≤ τ - ε
              · exact Or.inl ⟨hx, h⟩
              · exact Or.inr ⟨lt_of_not_ge h, hx2⟩
            have hm := le_trans (MeasureTheory.measure_mono (μ := MeasureTheory.volume) hsub)
              (MeasureTheory.measure_union_le _ _)
            rw [F6, Real.volume_Ioo] at hm
            have hm2 := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨Gfin i _, ENNReal.ofReal_ne_top⟩) hm
            rw [ENNReal.toReal_add (Gfin i _) ENNReal.ofReal_ne_top, ENNReal.toReal_natCast,
              ENNReal.toReal_ofReal (by linarith)] at hm2
            have hin : α * (p i : ℝ) ≤ (MeasureTheory.volume (lpSet p r i ∩ Set.Iic ((τ:ℝ) - ε))).toReal := by
              have : (τ:ℝ) - ((τ:ℝ) - ε) = ε := by ring
              rw [this] at hm2; linarith
            have := csInf_le ⟨(r i : ℝ), fun t ht => Gb i t ht⟩ (show (τ:ℝ) - ε ∈ {t : ℝ | α * (p i : ℝ) ≤
              (MeasureTheory.volume (lpSet p r i ∩ Set.Iic t)).toReal} from hin)
            have : alphaPoint p (lpSet p r) i α ≤ (τ:ℝ) - ε := this
            linarith
          have G4 : ∀ i (τ : ℕ), alphaPoint p (lpSet p r) i α ≤ τ →
              α * p i ≤ ((p i - lpRemaining p r τ i : ℕ) : ℝ) := by
            intro i τ hτ
            by_contra hc
            push Not at hc
            set d : ℝ := ((p i - lpRemaining p r τ i : ℕ) : ℝ)
            have hne : {t : ℝ | α * (p i : ℝ) ≤
                (MeasureTheory.volume (lpSet p r i ∩ Set.Iic t)).toReal}.Nonempty := by
              refine ⟨τ0, ?_⟩
              show α * (p i : ℝ) ≤ (MeasureTheory.volume (lpSet p r i ∩ Set.Iic (τ0:ℝ))).toReal
              have h1 : (MeasureTheory.volume (lpSet p r i ∩ Set.Iio (τ0:ℝ))).toReal ≤
                  (MeasureTheory.volume (lpSet p r i ∩ Set.Iic (τ0:ℝ))).toReal :=
                ENNReal.toReal_mono (Gfin i _) (MeasureTheory.measure_mono
                  (Set.inter_subset_inter_right _ Set.Iio_subset_Iic_self))
              rw [F6, hτ0] at h1
              simp only [Nat.sub_zero, ENNReal.toReal_natCast] at h1
              have : (0:ℝ) ≤ p i := by positivity
              nlinarith [hα.2]
            have hlt : sInf {t : ℝ | α * (p i : ℝ) ≤
                (MeasureTheory.volume (lpSet p r i ∩ Set.Iic t)).toReal} < (τ:ℝ) + (α * p i - d) := by
              have : alphaPoint p (lpSet p r) i α < (τ:ℝ) + (α * p i - d) := by linarith
              exact this
            obtain ⟨t', ht', ht'lt⟩ := exists_lt_of_csInf_lt hne hlt
            have ht'' : α * (p i : ℝ) ≤ (MeasureTheory.volume (lpSet p r i ∩ Set.Iic t')).toReal := ht'
            have hsub : lpSet p r i ∩ Set.Iic t' ⊆
                (lpSet p r i ∩ Set.Iio (τ:ℝ)) ∪ Set.Icc (τ:ℝ) (max t' τ) := by
              intro x ⟨hx, hx2⟩
              by_cases h : x < τ
              · exact Or.inl ⟨hx, h⟩
              · exact Or.inr ⟨le_of_not_gt h, le_trans hx2 (le_max_left _ _)⟩
            have hm := le_trans (MeasureTheory.measure_mono (μ := MeasureTheory.volume) hsub)
              (MeasureTheory.measure_union_le _ _)
            rw [F6, Real.volume_Icc] at hm
            have hm2 := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr
              ⟨ENNReal.natCast_ne_top _, ENNReal.ofReal_ne_top⟩) hm
            rw [ENNReal.toReal_add (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top,
              ENNReal.toReal_natCast,
              ENNReal.toReal_ofReal (by linarith [le_max_right t' (τ:ℝ)])] at hm2
            have : max t' (τ:ℝ) < (τ:ℝ) + (α * p i - d) := max_lt ht'lt (by linarith)
            have e : ((p i - lpRemaining p r τ i : ℕ) : ℝ) = d := rfl
            rw [e] at hm2
            linarith
          have G5 : ∀ j (b : ℕ), lpRemaining p r b j = 0 → alphaPoint p (lpSet p r) j α ≤ b := by
            intro j b hb
            apply csInf_le ⟨(r j : ℝ), fun t ht => Gb j t ht⟩
            show α * (p j : ℝ) ≤ (MeasureTheory.volume (lpSet p r j ∩ Set.Iic (b:ℝ))).toReal
            have h1 : (MeasureTheory.volume (lpSet p r j ∩ Set.Iio (b:ℝ))).toReal ≤
                (MeasureTheory.volume (lpSet p r j ∩ Set.Iic (b:ℝ))).toReal :=
              ENNReal.toReal_mono (Gfin j _) (MeasureTheory.measure_mono
                (Set.inter_subset_inter_right _ Set.Iio_subset_Iic_self))
            rw [F6, hb] at h1
            simp only [Nat.sub_zero, ENNReal.toReal_natCast] at h1
            have : (0:ℝ) ≤ p j := by positivity
            nlinarith [hα.2]
          exact ⟨F5, ⟨τ0, hzero⟩, G2, G3, G4, G5⟩
        have hcore : ∀ (s : Fin n → ℝ) (T : ℝ), IsNonpreemptiveSchedule p r s →
            (∀ j, s j + (p j : ℝ) ≤ T) → 0 ≤ T → ∀ k j : Fin n,
            precedes p r (fun _ => α) k j →
            ((r k + ∑ i ∈ Finset.univ.filter
              (fun i => precedes p r (fun _ => α) k i ∧ precedes p r (fun _ => α) i j), p i : ℕ) : ℝ)
              ≤ (1 + α) * T := by
          intro s T hs hsT _ k j hkj
          obtain ⟨F5, _, G2, G3, _⟩ := hfacts s T hs hsT
          have hsumT := hsumT s T hs hsT
          set X := Finset.univ.filter (fun i => precedes p r (fun _ => α) k i ∧
            precedes p r (fun _ => α) i j)
          have hX : ∀ i ∈ X, ((r k : ℕ) : ℝ) ≤ alphaPoint p (lpSet p r) i α := by
            intro i hi
            have hi' := (Finset.mem_filter.mp hi).2.1
            simp only [precedes] at hi'
            have := G2 k
            rcases hi' with h | h
            · linarith
            · linarith [h.1]
          have hsplit : ∑ i ∈ X, (p i : ℝ) = ∑ i ∈ X, ((p i - lpRemaining p r (r k) i : ℕ) : ℝ) +
              ∑ i ∈ X, (lpRemaining p r (r k) i : ℝ) := by
            rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro i _
            rw [Nat.cast_sub (F1 _ i)]; ring
          have hA : ∑ i ∈ X, ((p i - lpRemaining p r (r k) i : ℕ) : ℝ) ≤ ∑ i, α * (p i : ℝ) :=
            le_trans (Finset.sum_le_sum (fun i hi => G3 i (r k) (hX i hi)))
              (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
                (fun i _ _ => by have := hα.1; positivity))
          have hB : ∑ i ∈ X, (lpRemaining p r (r k) i : ℝ) ≤ ∑ i, (lpRemaining p r (r k) i : ℝ) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => by positivity)
          have hC := F5 (r k)
          have hrk : (r k : ℝ) ≤ T := by
            have := hs.1 k; have := hsT k; have : (0:ℝ) ≤ p k := by positivity
            linarith
          rw [max_eq_right (by linarith)] at hC
          have hP : ∑ i, (p i : ℝ) ≤ T := by
            rcases hsumT 0 Finset.univ (fun i _ => by positivity) with h | h
            · linarith
            · exact absurd (h ▸ Finset.mem_univ k) (Finset.notMem_empty k)
          have hαP : ∑ i, α * (p i : ℝ) ≤ α * T := by
            rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left hP hα.1.le
          push_cast
          linarith
        have hne : {T : ℝ | 0 ≤ T ∧ ∃ s : Fin n → ℝ,
            IsNonpreemptiveSchedule p r s ∧ ∀ j, s j + (p j : ℝ) ≤ T}.Nonempty := by
          refine ⟨(∑ i, (r i : ℝ)) + ∑ i, (p i : ℝ), ?_, fun j => (∑ i, (r i : ℝ)) +
            ∑ i ∈ Finset.univ.filter (· < j), (p i : ℝ), ⟨?_, ?_⟩, ?_⟩
          · positivity
          · intro j
            have h1 : (r j : ℝ) ≤ ∑ i, (r i : ℝ) :=
              Finset.single_le_sum (f := fun i => (r i : ℝ)) (fun i _ => by positivity) (Finset.mem_univ j)
            have h3 : (0:ℝ) ≤ ∑ i ∈ Finset.univ.filter (· < j), (p i : ℝ) :=
              Finset.sum_nonneg (fun i _ => by positivity)
            simp only; linarith
          · have key : ∀ j k : Fin n, j < k → ∑ i ∈ Finset.univ.filter (· < j), (p i : ℝ) + p j ≤
                ∑ i ∈ Finset.univ.filter (· < k), (p i : ℝ) := by
              intro j k hjk
              have hsub : insert j (Finset.univ.filter (· < j)) ⊆ Finset.univ.filter (· < k) := by
                intro x hx
                simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
                rcases hx with rfl | hx
                · exact hjk
                · exact lt_trans hx hjk
              have := Finset.sum_le_sum_of_subset_of_nonneg hsub (f := fun i => (p i : ℝ))
                (fun i _ _ => by positivity)
              rw [Finset.sum_insert (by simp)] at this
              linarith
            intro j k hjk
            rcases lt_or_gt_of_ne hjk with h | h
            · left; have := key j k h; simp only; linarith
            · right; have := key k j h; simp only; linarith
          · intro j
            have hsub : insert j (Finset.univ.filter (· < j)) ⊆ Finset.univ := Finset.subset_univ _
            have := Finset.sum_le_sum_of_subset_of_nonneg hsub (f := fun i => (p i : ℝ))
                (fun i _ _ => by positivity)
            rw [Finset.sum_insert (by simp)] at this
            simp only; linarith
        have hCk : ∀ j, ∃ k, precedes p r (fun _ => α) k j ∧
            (alphaCompletion p r (fun _ => α) j : ℝ) = r k + ∑ i ∈ Finset.univ.filter
              (fun i => precedes p r (fun _ => α) k i ∧ precedes p r (fun _ => α) i j), (p i : ℝ) := by
          intro j
          unfold alphaCompletion listCompletion
          set F := Finset.univ.filter (fun k => precedes p r (fun _ => α) k j)
          have hjF : j ∈ F := by
            simp only [F, Finset.mem_filter, Finset.mem_univ, true_and]
            exact Or.inr ⟨rfl, le_refl _⟩
          obtain ⟨k, hk, hkeq⟩ := Finset.exists_mem_eq_sup F ⟨j, hjF⟩
            (fun k => r k + ∑ i ∈ Finset.univ.filter
              (fun i => precedes p r (fun _ => α) k i ∧ precedes p r (fun _ => α) i j), p i)
          refine ⟨k, by simpa [F] using hk, ?_⟩
          rw [hkeq]; push_cast; rfl
        have h3 : ∀ j, (alphaCompletion p r (fun _ => α) j : ℝ) ≤ (1 + α) * optMakespan p r := by
          intro j
          have hpos : (0:ℝ) < 1 + α := by linarith [hα.1]
          have hbound : ∀ T ∈ {T : ℝ | 0 ≤ T ∧ ∃ s : Fin n → ℝ,
              IsNonpreemptiveSchedule p r s ∧ ∀ j, s j + (p j : ℝ) ≤ T},
              (alphaCompletion p r (fun _ => α) j : ℝ) / (1 + α) ≤ T := by
            rintro T ⟨hT0, s, hs, hsT⟩
            rw [div_le_iff₀ hpos]
            unfold alphaCompletion listCompletion
            set F := Finset.univ.filter (fun k => precedes p r (fun _ => α) k j)
            have hjF : j ∈ F := by
              simp only [F, Finset.mem_filter, Finset.mem_univ, true_and]
              exact Or.inr ⟨rfl, le_refl _⟩
            obtain ⟨k, hk, hkeq⟩ := Finset.exists_mem_eq_sup F ⟨j, hjF⟩
              (fun k => r k + ∑ i ∈ Finset.univ.filter
                (fun i => precedes p r (fun _ => α) k i ∧ precedes p r (fun _ => α) i j), p i)
            have hkF : precedes p r (fun _ => α) k j := by
              simpa [F] using hk
            have hc := hcore s T hs hsT hT0 k j hkF
            have : ((F.sup (fun k => r k + ∑ i ∈ Finset.univ.filter
                (fun i => precedes p r (fun _ => α) k i ∧ precedes p r (fun _ => α) i j), p i) : ℕ) : ℝ)
                ≤ (1 + α) * T := by rw [hkeq]; exact hc
            linarith
          have := le_csInf hne hbound
          unfold optMakespan
          rw [div_le_iff₀ hpos] at this
          linarith
        have h1 : ∑ j, w j * (alphaCompletion p r (fun _ => α) j : ℝ) ≤
            max (1 + 1 / α) (1 + 2 * α) * Shared.zR p r w := by
          set c := max (1 + 1 / α) (1 + 2 * α) with hcdef
          have hc : 0 < c := lt_of_lt_of_le (by linarith [hα.1]) (le_max_right _ _)
          have hfe : {M : Fin n → ℝ | Shared.FeasibleR p r M}.Nonempty := by
            refine ⟨fun _ => (∑ i, (r i : ℝ)) + ∑ i, (p i : ℝ), ?_⟩
            intro S hS
            have hps : 0 ≤ Shared.pSum p S := Finset.sum_nonneg (fun i _ => by positivity)
            have hpS : Shared.pSum p S ≤ ∑ i, (p i : ℝ) :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => by positivity)
            obtain ⟨j0, hj0⟩ := hS
            have hrm : Shared.rmin r S ⟨j0, hj0⟩ ≤ ∑ i, (r i : ℝ) :=
              le_trans (Finset.inf'_le _ hj0) (Finset.single_le_sum (f := fun i => (r i : ℝ))
                (fun i _ => by positivity) (Finset.mem_univ j0))
            rw [← Finset.sum_mul]
            change Shared.pSum p S * _ ≤ Shared.pSum p S * _
            apply mul_le_mul_of_nonneg_left _ hps
            linarith
          have hpre : ∀ M, Shared.FeasibleR p r M → ∀ m : ℕ,
              ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < m),
                (p i : ℝ) * (alphaCompletion p r (fun _ => α) i : ℝ) ≤
              c * ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < m),
                (p i : ℝ) * (M i + (p i : ℝ) / 2) := by
            intro M hM m
            obtain ⟨T, _, s, hs, hsT⟩ := hne
            obtain ⟨_, ⟨τ0, hzero⟩, G2, G3, G4, G5⟩ := hfacts s T hs hsT
            have F7 : ∀ τ j, lpRun p r τ = some j → ∀ i, r i ≤ τ → 0 < lpRemaining p r τ i → j ≤ i := by
              intro τ j h i hi1 hi2
              unfold lpRun lpPick at h
              split_ifs at h with hne
              rw [Option.some_inj] at h
              rw [← h]
              exact Finset.min'_le _ _ (by simp [hi1, hi2])
            have F8 : ∀ i σ, σ ≤ r i → lpRemaining p r σ i = p i := by
              intro i σ
              induction σ with
              | zero => intro _; rfl
              | succ σ ih =>
                intro h
                rw [F4, if_neg, ih (by omega)]
                intro hr; have := (F2 σ i hr).1; omega
            have F9 : ∀ i σ σ', σ ≤ σ' → lpRemaining p r σ' i ≤ lpRemaining p r σ i := by
              intro i σ σ' h
              induction σ', h using Nat.le_induction with
              | base => exact le_refl _
              | succ σ' _ ih => exact le_trans (Fmono σ' i) ih
            have he : ∀ τ i, (lpRemaining p r (τ+1) i : ℝ) = lpRemaining p r τ i -
                if lpRun p r τ = some i then 1 else 0 := by
              intro τ i
              rw [F4]
              by_cases hj : lpRun p r τ = some i
              · have := (F2 τ i hj).2
                rw [if_pos hj, if_pos hj, Nat.cast_sub (by omega)]; simp
              · rw [if_neg hj, if_neg hj]; simp
            have hone : ∀ τ i0 (S : Finset (Fin n)), lpRun p r τ = some i0 → i0 ∈ S →
                ∑ i ∈ S, (lpRemaining p r (τ+1) i : ℝ) = ∑ i ∈ S, (lpRemaining p r τ i : ℝ) - 1 := by
              intro τ i0 S h hS
              simp only [he]
              rw [Finset.sum_sub_distrib]
              congr 1
              rw [h]
              simp [hS]
            have F10 : ∀ σ : ℕ, ∑ i, ((p i : ℝ) - lpRemaining p r σ i) ≤ σ := by
              intro σ
              induction σ with
              | zero => simp [lpRemaining]
              | succ σ ih =>
                rw [Finset.sum_sub_distrib] at ih ⊢
                rcases hrun : lpRun p r σ with _ | j0
                · have : ∀ i, (lpRemaining p r (σ+1) i : ℝ) = lpRemaining p r σ i := by
                    intro i; rw [he, hrun]; simp
                  simp only [this]; push_cast; linarith
                · rw [hone σ j0 _ hrun (Finset.mem_univ _)]; push_cast; linarith
            -- total order facts
            have Pt : ∀ i k, precedes p r (fun _ => α) i k ∨ precedes p r (fun _ => α) k i := by
              intro i k
              unfold precedes
              rcases lt_trichotomy (alphaPoint p (lpSet p r) i α) (alphaPoint p (lpSet p r) k α) with h | h | h
              · exact Or.inl (Or.inl h)
              · rcases le_total i k with h' | h'
                · exact Or.inl (Or.inr ⟨h, h'⟩)
                · exact Or.inr (Or.inr ⟨h.symm, h'⟩)
              · exact Or.inr (Or.inl h)
            have Pa : ∀ i k, precedes p r (fun _ => α) i k → precedes p r (fun _ => α) k i → i = k := by
              intro i k h1 h2
              unfold precedes at h1 h2
              rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
              · exact absurd h1 (lt_asymm h2)
              · rw [h2.1] at h1; exact absurd h1 (lt_irrefl _)
              · rw [h1.1] at h2; exact absurd h2 (lt_irrefl _)
              · exact le_antisymm h1.2 h2.2
            have Ple : ∀ i k, precedes p r (fun _ => α) i k →
                alphaPoint p (lpSet p r) i α ≤ alphaPoint p (lpSet p r) k α := by
              intro i k h
              rcases h with h | h
              · exact h.le
              · exact h.1.le
            have Ptr : ∀ i k l, precedes p r (fun _ => α) i k → precedes p r (fun _ => α) k l →
                precedes p r (fun _ => α) i l := by
              intro i k l h1 h2
              unfold precedes at *
              rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
              · exact Or.inl (lt_trans h1 h2)
              · exact Or.inl (lt_of_lt_of_eq h1 h2.1)
              · exact Or.inl (lt_of_eq_of_lt h1.1 h2)
              · exact Or.inr ⟨h1.1.trans h2.1, le_trans h1.2 h2.2⟩
            -- one busy block
            have hblock : ∀ (a b : ℕ) (S : Finset (Fin n)), a ≤ b →
                (∀ i ∈ S, a ≤ r i ∧ r i < b) →
                (∀ σ, a ≤ σ → σ < b → ∃ i ∈ S, lpRun p r σ = some i) →
                (∀ i ∈ S, lpRemaining p r b i = 0) →
                ∑ i ∈ S, (p i : ℝ) * (alphaCompletion p r (fun _ => α) i : ℝ) ≤
                  c * ∑ i ∈ S, (p i : ℝ) * (M i + (p i : ℝ) / 2) := by
              intro a b S hab hSr hSrun hSb
              by_cases hSne : S.Nonempty
              swap
              · rw [Finset.not_nonempty_iff_eq_empty] at hSne; simp [hSne]
              set P : ℝ := ∑ i ∈ S, (p i : ℝ) with hP
              have hP0 : 0 ≤ P := Finset.sum_nonneg (fun i _ => by positivity)
              have hwork : ∀ d : ℕ, a + d ≤ b →
                  ∑ i ∈ S, (lpRemaining p r (a + d) i : ℝ) = P - d := by
                intro d
                induction d with
                | zero =>
                  intro _
                  simp only [Nat.add_zero, Nat.cast_zero, sub_zero, hP]
                  apply Finset.sum_congr rfl; intro i hi; rw [F8 i a (hSr i hi).1]
                | succ d ih =>
                  intro h
                  obtain ⟨i0, hi0, hrun⟩ := hSrun (a+d) (by omega) (by omega)
                  rw [← Nat.add_assoc, hone (a+d) i0 S hrun hi0, ih (by omega)]; push_cast; ring
              have hout : ∀ i ∉ S, ∀ d : ℕ, a + d ≤ b → lpRemaining p r (a+d) i = lpRemaining p r a i := by
                intro i hi d
                induction d with
                | zero => intro _; rfl
                | succ d ih =>
                  intro h
                  obtain ⟨i0, hi0, hrun⟩ := hSrun (a+d) (by omega) (by omega)
                  rw [← Nat.add_assoc, F4, if_neg, ih (by omega)]
                  rw [hrun]; intro h'; rw [Option.some_inj] at h'; exact hi (h' ▸ hi0)
              have hG : ∀ i j, j ∈ S → i ∉ S → precedes p r (fun _ => α) i j →
                  α * p i ≤ (p i : ℝ) - lpRemaining p r a i := by
                intro i j hj hi hij
                have h1 : alphaPoint p (lpSet p r) j α ≤ b := by
                  by_contra hcon
                  push Not at hcon
                  exact absurd hcon (not_lt.mpr (G5 j b (hSb j hj)))
                have h2 := G4 i b (le_trans (Ple i j hij) h1)
                have h3 := hout i hi (b - a) (by omega)
                rw [Nat.add_sub_cancel' hab] at h3
                rw [h3, Nat.cast_sub (F1 a i)] at h2
                exact h2
              have hjob : ∀ j ∈ S, (alphaCompletion p r (fun _ => α) j : ℝ) ≤
                  (1 + 1 / α) * a + α * P +
                    ∑ i ∈ S.filter (fun i => precedes p r (fun _ => α) i j), (p i : ℝ) := by
                intro j hj
                obtain ⟨k, hkj, hC⟩ := hCk j
                rw [hC]
                have hout_sum : ∑ i ∈ (Finset.univ.filter (fun i => precedes p r (fun _ => α) k i ∧
                    precedes p r (fun _ => α) i j)).filter (fun i => i ∉ S), (p i : ℝ) ≤ 1 / α * a := by
                  have h1 : ∑ i ∈ (Finset.univ.filter (fun i => precedes p r (fun _ => α) k i ∧
                    precedes p r (fun _ => α) i j)).filter (fun i => i ∉ S), α * (p i : ℝ) ≤ a := by
                    refine le_trans ?_ (F10 a)
                    refine le_trans (Finset.sum_le_sum (g := fun i => (p i : ℝ) - lpRemaining p r a i) ?_) ?_
                    · intro i hi
                      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
                      exact hG i j hj hi.2 hi.1.2
                    · apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
                      intro i _ _
                      have : (lpRemaining p r a i : ℝ) ≤ p i := by exact_mod_cast F1 a i
                      linarith
                  rw [← Finset.mul_sum] at h1
                  rw [one_div, inv_mul_eq_div, le_div_iff₀ hα.1]; linarith
                rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ.filter
                  (fun i => precedes p r (fun _ => α) k i ∧ precedes p r (fun _ => α) i j)) (fun i => i ∈ S)]
                have hmain : (r k : ℝ) + ∑ i ∈ (Finset.univ.filter
                    (fun i => precedes p r (fun _ => α) k i ∧ precedes p r (fun _ => α) i j)).filter
                    (fun i => i ∈ S), (p i : ℝ) ≤ a + α * P +
                    ∑ i ∈ S.filter (fun i => precedes p r (fun _ => α) i j), (p i : ℝ) := by
                  have hset : (Finset.univ.filter
                      (fun i => precedes p r (fun _ => α) k i ∧ precedes p r (fun _ => α) i j)).filter
                      (fun i => i ∈ S) = (S.filter (fun i => precedes p r (fun _ => α) i j)).filter
                      (fun i => precedes p r (fun _ => α) k i) := by
                    ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; tauto
                  rw [hset]
                  rw [← Finset.sum_filter_add_sum_filter_not
                    (S.filter (fun i => precedes p r (fun _ => α) i j)) (fun i => precedes p r (fun _ => α) k i)]
                  by_cases hkS : k ∈ S
                  · have hrk := hSr k hkS
                    have hw1 := hwork (r k - a) (by omega)
                    rw [Nat.add_sub_cancel' hrk.1, Nat.cast_sub hrk.1] at hw1
                    have hw2 : (r k : ℝ) = a + ∑ i ∈ S, ((p i : ℝ) - lpRemaining p r (r k) i) := by
                      rw [Finset.sum_sub_distrib, hw1]; ring
                    have hw3 : ∑ i ∈ S, ((p i : ℝ) - lpRemaining p r (r k) i) ≤
                        ∑ i ∈ S, (α * p i + if precedes p r (fun _ => α) k i then 0 else (p i : ℝ)) := by
                      apply Finset.sum_le_sum
                      intro i _
                      have hα0 := hα.1
                      by_cases hki : precedes p r (fun _ => α) k i
                      · rw [if_pos hki]
                        have := G3 i (r k) (le_trans (G2 k) (Ple k i hki))
                        rw [Nat.cast_sub (F1 _ i)] at this
                        linarith
                      · rw [if_neg hki]
                        have h1 : (0:ℝ) ≤ lpRemaining p r (r k) i := by positivity
                        have h2 : (0:ℝ) ≤ α * p i := by positivity
                        linarith
                    rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hw3
                    have hw4 : ∑ i ∈ S, (if precedes p r (fun _ => α) k i then 0 else (p i : ℝ)) =
                        ∑ i ∈ (S.filter (fun i => precedes p r (fun _ => α) i j)).filter
                          (fun i => ¬ precedes p r (fun _ => α) k i), (p i : ℝ) := by
                      rw [Finset.filter_filter, Finset.sum_filter]
                      apply Finset.sum_congr rfl
                      intro i _
                      by_cases hki : precedes p r (fun _ => α) k i
                      · simp [hki]
                      · have : precedes p r (fun _ => α) i j :=
                          Ptr i k j ((Pt i k).resolve_right hki) hkj
                        simp [hki, this]
                    rw [hw4] at hw3
                    linarith
                  · have h1 := hG k j hj hkS hkj
                    have h2 : r k ≤ a := by
                      by_contra hcon
                      rw [F8 k a (by omega)] at h1
                      have : (0:ℝ) < p k := by exact_mod_cast hp k
                      nlinarith [hα.1]
                    have h2' : (r k : ℝ) ≤ a := by exact_mod_cast h2
                    have h3 : (0:ℝ) ≤ α * P := mul_nonneg hα.1.le hP0
                    have h4 : 0 ≤ ∑ i ∈ (S.filter (fun i => precedes p r (fun _ => α) i j)).filter
                          (fun i => ¬ precedes p r (fun _ => α) k i), (p i : ℝ) :=
                      Finset.sum_nonneg (fun i _ => by positivity)
                    linarith
                linarith
              have hQ : 2 * ∑ j ∈ S, (p j : ℝ) * ∑ i ∈ S.filter (fun i => precedes p r (fun _ => α) i j), (p i : ℝ)
                  = P * P + ∑ j ∈ S, (p j : ℝ) * p j := by
                have e1 : ∑ j ∈ S, (p j : ℝ) * ∑ i ∈ S.filter (fun i => precedes p r (fun _ => α) i j), (p i : ℝ)
                    = ∑ j ∈ S, ∑ i ∈ S, (if precedes p r (fun _ => α) i j then (p j : ℝ) * p i else 0) := by
                  apply Finset.sum_congr rfl; intro j _
                  rw [Finset.mul_sum, Finset.sum_filter]
                have e2 : ∑ j ∈ S, ∑ i ∈ S, (if precedes p r (fun _ => α) i j then (p j : ℝ) * p i else 0)
                    = ∑ j ∈ S, ∑ i ∈ S, (if precedes p r (fun _ => α) j i then (p j : ℝ) * p i else 0) := by
                  rw [Finset.sum_comm]
                  apply Finset.sum_congr rfl; intro j _
                  apply Finset.sum_congr rfl; intro i _
                  rw [mul_comm]
                rw [two_mul, e1]
                nth_rewrite 2 [e2]
                rw [← Finset.sum_add_distrib, hP, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
                apply Finset.sum_congr rfl; intro j hj
                rw [← Finset.sum_add_distrib]
                have e3 : (p j : ℝ) * p j = ∑ i ∈ S, (if j = i then (p j : ℝ) * p i else 0) := by
                  rw [Finset.sum_ite_eq, if_pos hj]
                rw [e3, ← Finset.sum_add_distrib]
                apply Finset.sum_congr rfl; intro i _
                by_cases hji : j = i
                · subst hji
                  have : precedes p r (fun _ => α) j j := Or.inr ⟨rfl, le_refl _⟩
                  simp [this]
                · rcases Pt i j with h | h
                  · have h' : ¬ precedes p r (fun _ => α) j i := fun h' => hji (Pa _ _ h' h)
                    simp [h, h', hji]
                  · have h' : ¬ precedes p r (fun _ => α) i j := fun h' => hji (Pa _ _ h h')
                    simp [h, h', hji]
              have hsum : ∑ j ∈ S, (p j : ℝ) * (alphaCompletion p r (fun _ => α) j : ℝ) ≤
                  ((1 + 1 / α) * a + α * P) * P + ∑ j ∈ S, (p j : ℝ) *
                    ∑ i ∈ S.filter (fun i => precedes p r (fun _ => α) i j), (p i : ℝ) := by
                rw [hP, Finset.mul_sum, ← Finset.sum_add_distrib]
                apply Finset.sum_le_sum; intro j hj
                have := mul_le_mul_of_nonneg_left (hjob j hj) (show (0:ℝ) ≤ p j by positivity)
                rw [← hP]; linarith
              have hMS := hM S hSne
              have hrm : (a : ℝ) ≤ Shared.rmin r S hSne :=
                Finset.le_inf' _ _ (fun i hi => by exact_mod_cast (hSr i hi).1)
              have hMS2 : P * (a + P / 2) ≤ ∑ j ∈ S, (p j : ℝ) * M j := by
                refine le_trans ?_ hMS
                change P * _ ≤ P * (_ + P / 2)
                apply mul_le_mul_of_nonneg_left _ hP0; linarith
              have e4 : ∑ i ∈ S, (p i : ℝ) * (M i + (p i : ℝ) / 2) =
                  ∑ j ∈ S, (p j : ℝ) * M j + (∑ j ∈ S, (p j : ℝ) * p j) / 2 := by
                rw [Finset.sum_div, ← Finset.sum_add_distrib]
                apply Finset.sum_congr rfl; intro j _; ring
              rw [e4]
              set QQ := ∑ j ∈ S, (p j : ℝ) * p j
              have hQ0 : 0 ≤ QQ := Finset.sum_nonneg (fun i _ => by positivity)
              have hc1 : 1 + 1 / α ≤ c := le_max_left _ _
              have hc2 : 1 + 2 * α ≤ c := le_max_right _ _
              have hc3 : 1 ≤ c := by linarith [hα.1]
              have ha0 : (0:ℝ) ≤ a := by positivity
              have k1 : (1 + 1 / α) * (a * P) ≤ c * (a * P) :=
                mul_le_mul_of_nonneg_right hc1 (mul_nonneg ha0 hP0)
              have k2 : (1 + 2 * α) * (P * P / 2) ≤ c * (P * P / 2) :=
                mul_le_mul_of_nonneg_right hc2 (by positivity)
              have k3 : 1 * (QQ / 2) ≤ c * (QQ / 2) := mul_le_mul_of_nonneg_right hc3 (by linarith)
              have k4 := mul_le_mul_of_nonneg_left hMS2 hc.le
              nlinarith [k1, k2, k3, k4, hsum, hQ]
            -- sweep over time
            have hsweep : ∀ τ : ℕ, ∃ a : ℕ, a ≤ τ ∧
                (∀ i : Fin n, i.val < m → r i < a → lpRemaining p r a i = 0) ∧
                (∀ σ, a ≤ σ → σ < τ → ∃ i : Fin n, i.val < m ∧ lpRun p r σ = some i) ∧
                ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < m ∧ r i < a),
                  (p i : ℝ) * (alphaCompletion p r (fun _ => α) i : ℝ) ≤
                c * ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < m ∧ r i < a),
                  (p i : ℝ) * (M i + (p i : ℝ) / 2) := by
              intro τ
              induction τ with
              | zero =>
                refine ⟨0, le_refl _, by simp, by intro σ h1 h2; omega, by simp⟩
              | succ τ ih =>
                obtain ⟨a, haτ, hclear, hbusy, hsum⟩ := ih
                by_cases hr : ∃ i : Fin n, i.val < m ∧ lpRun p r τ = some i
                · refine ⟨a, by omega, hclear, ?_, hsum⟩
                  intro σ h1 h2
                  rcases Nat.lt_succ_iff_lt_or_eq.mp h2 with h | h
                  · exact hbusy σ h1 h
                  · rw [h]; exact hr
                · have hdone : ∀ i : Fin n, i.val < m → r i ≤ τ → lpRemaining p r τ i = 0 := by
                    intro i him hiτ
                    by_contra hcon
                    have hpos := Nat.pos_of_ne_zero hcon
                    rcases hrun : lpRun p r τ with _ | j0
                    · have := F3 τ hrun i hpos; omega
                    · have h1 := F7 τ j0 hrun i hiτ hpos
                      exact hr ⟨j0, lt_of_le_of_lt (by exact_mod_cast h1) him, hrun⟩
                  have hlt : ∀ i : Fin n, i.val < m → r i ≤ τ → r i < τ := by
                    intro i him hiτ
                    by_contra hcon
                    have h1 := hdone i him hiτ
                    rw [F8 i τ (by omega)] at h1
                    have := hp i; omega
                  refine ⟨τ + 1, le_refl _, ?_, by intro σ h1 h2; omega, ?_⟩
                  · intro i him hi
                    have h1 := hdone i him (by omega)
                    have := Fmono τ i; omega
                  · have hbl := hblock a τ (Finset.univ.filter
                      (fun i : Fin n => i.val < m ∧ a ≤ r i ∧ r i < τ)) haτ
                      (by intro i hi; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
                          exact hi.2)
                      (by
                        intro σ h1 h2
                        obtain ⟨i, him, hrun⟩ := hbusy σ h1 h2
                        refine ⟨i, ?_, hrun⟩
                        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
                        have h3 := F2 σ i hrun
                        refine ⟨him, ?_, by omega⟩
                        by_contra hcon
                        have h4 := hclear i him (by omega)
                        have h5 := F9 i a σ h1
                        omega)
                      (by intro i hi; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
                          exact hdone i hi.1 (by omega))
                    have hU : Finset.univ.filter (fun i : Fin n => i.val < m ∧ r i < τ + 1) =
                        Finset.univ.filter (fun i : Fin n => i.val < m ∧ r i < a) ∪
                        Finset.univ.filter (fun i : Fin n => i.val < m ∧ a ≤ r i ∧ r i < τ) := by
                      ext i
                      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
                      constructor
                      · rintro ⟨h1, h2⟩
                        have := hlt i h1 (by omega)
                        by_cases h3 : r i < a
                        · exact Or.inl ⟨h1, h3⟩
                        · exact Or.inr ⟨h1, by omega, this⟩
                      · rintro (⟨h1, h2⟩ | ⟨h1, h2, h3⟩)
                        · exact ⟨h1, by omega⟩
                        · exact ⟨h1, by omega⟩
                    have hD : Disjoint (Finset.univ.filter (fun i : Fin n => i.val < m ∧ r i < a))
                        (Finset.univ.filter (fun i : Fin n => i.val < m ∧ a ≤ r i ∧ r i < τ)) := by
                      rw [Finset.disjoint_left]
                      intro i h1 h2
                      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
                      omega
                    rw [hU, Finset.sum_union hD, Finset.sum_union hD, mul_add]
                    linarith
            set N := τ0 + ∑ i, r i with hN
            have hrN : ∀ i, r i ≤ N := by
              intro i
              have := Finset.single_le_sum (f := r) (fun i _ => Nat.zero_le _) (Finset.mem_univ i)
              omega
            obtain ⟨a, haN, _, hbusy, hsum⟩ := hsweep (N + 1)
            have haN' : a = N + 1 := by
              by_contra hcon
              obtain ⟨i, _, hrun⟩ := hbusy N (by omega) (by omega)
              have h1 := (F2 N i hrun).2
              have h2 := hzero N i (by omega)
              omega
            have hset : Finset.univ.filter (fun i : Fin n => i.val < m ∧ r i < a) =
                Finset.univ.filter (fun i : Fin n => i.val < m) := by
              ext i
              simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              have := hrN i
              constructor
              · exact fun h => h.1
              · exact fun h => ⟨h, by omega⟩
            rw [hset] at hsum
            exact hsum
          have habel : ∀ (a : Fin n → ℝ), (∀ m : ℕ, 0 ≤ ∑ i ∈ Finset.univ.filter
              (fun i : Fin n => i.val < m), a i) → ∀ N : ℕ, N ≤ n → ∀ y : ℝ, 0 ≤ y →
              (∀ i : Fin n, i.val < N → y ≤ w i / p i) →
              y * ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < N), a i ≤
              ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < N), w i / p i * a i := by
            intro a ha N
            induction N with
            | zero => intro _ y _ _; simp
            | succ N ih =>
              intro hN y hy hyi
              set j : Fin n := ⟨N, by omega⟩ with hj
              have hset : Finset.univ.filter (fun i : Fin n => i.val < N + 1) =
                  insert j (Finset.univ.filter (fun i : Fin n => i.val < N)) := by
                ext i
                simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, hj, Fin.ext_iff]
                omega
              have hnot : j ∉ Finset.univ.filter (fun i : Fin n => i.val < N) := by simp [hj]
              have hρ : 0 ≤ w j / p j := div_nonneg (hw j).le (by positivity)
              have h1 := ih (by omega) (w j / p j) hρ (fun i hi => hsort i j (by
                rw [Fin.le_def, hj]; exact hi.le))
              have h2 := mul_le_mul_of_nonneg_right (hyi j (by simp [hj])) (ha (N+1))
              rw [hset, Finset.sum_insert hnot] at h2
              rw [hset, Finset.sum_insert hnot, Finset.sum_insert hnot]
              rw [mul_add] at h2 ⊢
              rw [mul_add] at h2
              linarith
          have hb : ∀ M, Shared.FeasibleR p r M →
              ∑ j, w j * (alphaCompletion p r (fun _ => α) j : ℝ) ≤ c * Shared.objR p w M := by
            intro M hM
            have h := habel (fun i => (p i : ℝ) * (c * (M i + (p i : ℝ) / 2) -
              (alphaCompletion p r (fun _ => α) i : ℝ))) (by
                intro m
                have := hpre M hM m
                rw [Finset.mul_sum] at this
                have e : ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < m),
                    (p i : ℝ) * (c * (M i + (p i : ℝ) / 2) - (alphaCompletion p r (fun _ => α) i : ℝ)) =
                    ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < m),
                      c * ((p i : ℝ) * (M i + (p i : ℝ) / 2)) -
                    ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < m),
                      (p i : ℝ) * (alphaCompletion p r (fun _ => α) i : ℝ) := by
                  rw [← Finset.sum_sub_distrib]
                  apply Finset.sum_congr rfl; intro i _; ring
                rw [e]; linarith) n le_rfl 0 le_rfl
                (fun i _ => div_nonneg (hw i).le (by positivity))
            have hU : Finset.univ.filter (fun i : Fin n => i.val < n) = Finset.univ := by
              ext i; simp
            rw [hU, zero_mul] at h
            have e : ∑ i, w i / p i * ((p i : ℝ) * (c * (M i + (p i : ℝ) / 2) -
                (alphaCompletion p r (fun _ => α) i : ℝ))) =
                c * Shared.objR p w M - ∑ j, w j * (alphaCompletion p r (fun _ => α) j : ℝ) := by
              unfold Shared.objR
              rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
              apply Finset.sum_congr rfl; intro i _
              have : (p i : ℝ) ≠ 0 := by have := hp i; positivity
              field_simp
            rw [e] at h
            linarith
          have := le_csInf (hfe.image (fun M => Shared.objR p w M))
            (a := (∑ j, w j * (alphaCompletion p r (fun _ => α) j : ℝ)) / c) (by
              rintro _ ⟨M, hM, rfl⟩
              rw [div_le_iff₀ hc, mul_comm]; exact hb M hM)
          unfold Shared.zR
          rw [div_le_iff₀ hc] at this
          linarith
        exact ⟨h1, h2, h3⟩
