-- Prove2me | solution 1 for RobustInventory.SingleStation.Supplement.theorem_2_1
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:06:20.245023+00:00
-- url     : https://prove2.me/submissions/d8d7aa8b-9c93-4656-9b84-6dfb8128dba8

import Definitions.Def_RobustInventory_SingleStation_Supplement_BudgetedLP

open RobustInventory
open RobustInventory.SingleStation
open RobustInventory.SingleStation.Supplement

/-- Theorem 2.1, p. 152: the linear program (2) is the robust counterpart of (1).
1. `x` is feasible for (1) iff it extends to a feasible point of (2).
2. `x` is optimal for (1) iff it is the `x`-part of an optimal point of (2).
3. The two problems have the same set of objective values, hence the same optimal value. -/
theorem solution {m n : ℕ} (P : BudgetedLP m n) :
    (∀ x, P.RobustFeasible x ↔ ∃ q r y, P.CounterpartFeasible x q r y) ∧
    (∀ x, P.IsRobustOptimal x ↔ ∃ q r y, P.IsCounterpartOptimal x q r y) ∧
    {v : ℝ | ∃ x, P.RobustFeasible x ∧ v = P.cost x} =
      {v : ℝ | ∃ x q r y, P.CounterpartFeasible x q r y ∧ v = P.cost x} := by
        classical
        have hsplit : ∀ f : Fin m × Fin n → ℝ, (∀ ij, ij ∉ P.J → f ij = 0) →
            ∑ ij ∈ P.J, f ij = ∑ i', ∑ j ∈ Finset.univ.filter (fun j => (i', j) ∈ P.J), f (i', j) := by
          intro f hf
          rw [Finset.sum_subset (Finset.subset_univ P.J) (fun ij _ h => hf ij h)]
          rw [Fintype.sum_prod_type]
          refine Finset.sum_congr rfl (fun i' _ => ?_)
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          split_ifs with h
          · rfl
          · exact hf _ h
        have knap : ∀ (s : Finset (Fin n)) (v : Fin n → ℝ), (∀ j ∈ s, 0 ≤ v j) →
            ∃ q : ℝ, 0 ≤ q ∧ ∃ w : Fin n → ℝ, (∀ j, 0 ≤ w j ∧ w j ≤ 1) ∧
              ∑ j ∈ s, w j ≤ P.Γ ∧
              q * P.Γ + ∑ j ∈ s, max (v j - q) 0 ≤ ∑ j ∈ s, w j * v j := by
          intro s v hv
          set C : Finset ℝ := (insert 0 (s.image v)).filter
            (fun t => t = 0 ∨ P.Γ ≤ ((s.filter (fun j => t ≤ v j)).card : ℝ)) with hC
          have h0C : (0:ℝ) ∈ C := by
            rw [hC, Finset.mem_filter]; exact ⟨Finset.mem_insert_self _ _, Or.inl rfl⟩
          have hCne : C.Nonempty := ⟨0, h0C⟩
          set q := C.max' hCne with hqdef
          have hqC : q ∈ C := C.max'_mem hCne
          have hq0 : 0 ≤ q := C.le_max' 0 h0C
          have hqmax : ∀ t ∈ C, t ≤ q := fun t ht => C.le_max' t ht
          have hgt : ((s.filter (fun j => q < v j)).card : ℝ) ≤ P.Γ := by
            by_contra hcon
            push Not at hcon
            have hne : (s.filter (fun j => q < v j)).Nonempty := by
              rw [← Finset.card_pos]
              have : (0:ℝ) < ((s.filter (fun j => q < v j)).card : ℝ) := lt_of_le_of_lt P.hΓ hcon
              exact_mod_cast this
            set q' := ((s.filter (fun j => q < v j)).image v).min' (hne.image v) with hq'def
            have hq'mem := ((s.filter (fun j => q < v j)).image v).min'_mem (hne.image v)
            rw [← hq'def, Finset.mem_image] at hq'mem
            obtain ⟨k, hk, hkv⟩ := hq'mem
            rw [Finset.mem_filter] at hk
            have hq'le : ∀ j ∈ s.filter (fun j => q < v j), q' ≤ v j := fun j hj =>
              Finset.min'_le _ _ (Finset.mem_image_of_mem v hj)
            have hsub : s.filter (fun j => q < v j) ⊆ s.filter (fun j => q' ≤ v j) := by
              intro j hj
              have hj' := hj
              rw [Finset.mem_filter] at hj ⊢
              exact ⟨hj.1, hq'le j hj'⟩
            have hcard : ((s.filter (fun j => q < v j)).card : ℝ) ≤
                ((s.filter (fun j => q' ≤ v j)).card : ℝ) := by
              exact_mod_cast Finset.card_le_card hsub
            have hq'C : q' ∈ C := by
              rw [hC, Finset.mem_filter]
              exact ⟨Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨k, hk.1, hkv⟩), Or.inr (by linarith)⟩
            have := hqmax q' hq'C
            linarith [hk.2, hkv]
          rcases eq_or_lt_of_le hq0 with hq | hq
          · refine ⟨q, hq0, fun j => if q < v j then 1 else 0, ?_, ?_, ?_⟩
            · intro j; dsimp only; split_ifs <;> norm_num
            · rw [Finset.sum_boole]; simpa using hgt
            · rw [← hq, zero_mul, zero_add]
              apply Finset.sum_le_sum
              intro j hj
              have := hv j hj
              dsimp only
              split_ifs with h
              · rw [max_eq_left (by linarith)]; linarith
              · rw [max_eq_right (by linarith)]; simp
          · have hqT := (Finset.mem_filter.1 hqC)
            have hΓle : P.Γ ≤ ((s.filter (fun j => q ≤ v j)).card : ℝ) := by
              rcases hqT.2 with h | h
              · exact absurd h (ne_of_gt hq)
              · exact h
            have hqimg : q ∈ s.image v := by
              rcases Finset.mem_insert.1 hqT.1 with h | h
              · exact absurd h (ne_of_gt hq)
              · exact h
            obtain ⟨k0, hk0s, hk0v⟩ := Finset.mem_image.1 hqimg
            have hEpos : (0:ℝ) < ((s.filter (fun j => v j = q)).card : ℝ) := by
              have : 0 < (s.filter (fun j => v j = q)).card :=
                Finset.card_pos.2 ⟨k0, Finset.mem_filter.2 ⟨hk0s, hk0v⟩⟩
              exact_mod_cast this
            have hcardsplit : ((s.filter (fun j => q ≤ v j)).card : ℝ) =
                ((s.filter (fun j => q < v j)).card : ℝ) + ((s.filter (fun j => v j = q)).card : ℝ) := by
              have : s.filter (fun j => q ≤ v j) =
                  s.filter (fun j => q < v j) ∪ s.filter (fun j => v j = q) := by
                ext j
                simp only [Finset.mem_filter, Finset.mem_union]
                constructor
                · rintro ⟨h1, h2⟩
                  rcases lt_or_eq_of_le h2 with h | h
                  · exact Or.inl ⟨h1, h⟩
                  · exact Or.inr ⟨h1, h.symm⟩
                · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
                  · exact ⟨h1, h2.le⟩
                  · exact ⟨h1, h2.ge⟩
              rw [this, Finset.card_union_of_disjoint]
              · push_cast; ring
              · rw [Finset.disjoint_left]; intro j hj1 hj2
                rw [Finset.mem_filter] at hj1 hj2; linarith [hj1.2, hj2.2]
            set gc : ℝ := ((s.filter (fun j => q < v j)).card : ℝ) with hgc
            set ec : ℝ := ((s.filter (fun j => v j = q)).card : ℝ) with hec
            set θ := (P.Γ - gc) / ec with hθ
            have hθ0 : 0 ≤ θ := div_nonneg (by linarith) hEpos.le
            have hθ1 : θ ≤ 1 := by rw [hθ, div_le_one hEpos]; linarith
            have hθE : θ * ec = P.Γ - gc := by rw [hθ]; field_simp
            have hsum : ∑ j ∈ s, ((if q < v j then (1:ℝ) else 0) + (if v j = q then θ else 0)) = P.Γ := by
              rw [Finset.sum_add_distrib, Finset.sum_boole, ← Finset.sum_filter, Finset.sum_const,
                nsmul_eq_mul]
              rw [← hec]
              linarith
            refine ⟨q, hq0, fun j => (if q < v j then 1 else 0) + (if v j = q then θ else 0), ?_, hsum.le, ?_⟩
            · intro j
              by_cases h1 : q < v j
              · have h2 : ¬ v j = q := ne_of_gt h1
                simp [h1, h2]
              · by_cases h2 : v j = q
                · simp [h1, h2, hθ0, hθ1]
                · simp [h1, h2]
            · rw [← hsum, Finset.mul_sum, ← Finset.sum_add_distrib]
              apply Finset.sum_le_sum
              intro j hj
              rcases lt_trichotomy (v j) q with h | h | h
              · have h1 : ¬ q < v j := not_lt.2 h.le
                have h2 : ¬ v j = q := ne_of_lt h
                simp only [h1, h2, if_false]
                rw [max_eq_right (by linarith)]; simp
              · have h1 : ¬ q < v j := by rw [h]; exact lt_irrefl _
                simp only [h1, h, if_false, if_true]
                rw [max_eq_right (by linarith)]; ring_nf; rfl
              · have h2 : ¬ v j = q := ne_of_gt h
                simp only [h, h2, if_false, if_true]
                rw [max_eq_left (by linarith)]; linarith
        have part1 : ∀ x, P.RobustFeasible x ↔ ∃ q r y, P.CounterpartFeasible x q r y := by
          intro x
          constructor
          · rintro ⟨hbox, hrob⟩
            have hrow : ∀ i, ∃ qi : ℝ, 0 ≤ qi ∧ ∑ j, P.abar i j * x j + qi * P.Γ +
                ∑ j ∈ Finset.univ.filter (fun j => (i, j) ∈ P.J), max (P.ahat i j * |x j| - qi) 0
                  ≤ P.b i := by
              intro i
              obtain ⟨qi, hqi0, w, hw, hwsum, hwval⟩ := knap (Finset.univ.filter (fun j => (i, j) ∈ P.J))
                (fun j => P.ahat i j * |x j|) (by
                  intro j hj
                  rw [Finset.mem_filter] at hj
                  exact mul_nonneg (P.hahat _ hj.2) (abs_nonneg _))
              refine ⟨qi, hqi0, ?_⟩
              let sg : Fin n → ℝ := fun j => if 0 ≤ x j then 1 else -1
              have hsg : ∀ j, sg j * x j = |x j| := by
                intro j; simp only [sg]; split_ifs with h
                · rw [abs_of_nonneg h]; ring
                · rw [abs_of_neg (lt_of_not_ge h)]; ring
              have hsgabs : ∀ j, |sg j| = 1 := by intro j; simp only [sg]; split_ifs <;> norm_num
              let z : Fin m → Fin n → ℝ := fun i' j => if i' = i ∧ (i', j) ∈ P.J then w j * sg j else 0
              have hzJ : ∀ i' j, (i', j) ∉ P.J → z i' j = 0 := by
                intro i' j h; simp only [z]; rw [if_neg]; tauto
              have hzabs : ∀ i' j, |z i' j| ≤ 1 := by
                intro i' j; simp only [z]; split_ifs
                · rw [abs_mul, hsgabs, mul_one, abs_of_nonneg (hw j).1]; exact (hw j).2
                · simp
              have hzsum : ∑ ij ∈ P.J, |z ij.1 ij.2| ≤ P.Γ := by
                rw [hsplit (fun ij => |z ij.1 ij.2|) (fun ij h => by simp only [hzJ ij.1 ij.2 h, abs_zero])]
                rw [Finset.sum_eq_single i]
                · refine le_trans (le_of_eq ?_) hwsum
                  refine Finset.sum_congr rfl (fun j hj => ?_)
                  rw [Finset.mem_filter] at hj
                  simp only [z]
                  rw [if_pos (by simp [hj.2]), abs_mul, hsgabs, mul_one, abs_of_nonneg (hw j).1]
                · intro i' _ hi'
                  refine Finset.sum_eq_zero (fun j _ => ?_)
                  simp only [z]; rw [if_neg (by tauto)]; simp
                · intro h; exact absurd (Finset.mem_univ i) h
              have hA := hrob (fun i' j => P.abar i' j + P.ahat i' j * z i' j)
                ⟨z, hzJ, hzabs, hzsum, fun _ _ => rfl⟩ i
              simp only [Matrix.mulVec, dotProduct] at hA
              have hexp : ∑ j, (P.abar i j + P.ahat i j * z i j) * x j = ∑ j, P.abar i j * x j +
                  ∑ j ∈ Finset.univ.filter (fun j => (i, j) ∈ P.J), w j * (P.ahat i j * |x j|) := by
                rw [Finset.sum_filter, ← Finset.sum_add_distrib]
                refine Finset.sum_congr rfl (fun j _ => ?_)
                simp only [z]
                by_cases h : (i, j) ∈ P.J
                · rw [if_pos (by simp [h]), if_pos h, ← hsg j]; ring
                · rw [if_neg (by tauto), if_neg h]; ring
              linarith
            choose qf hqf0 hqf using hrow
            refine ⟨qf, fun i j => max (P.ahat i j * |x j| - qf i) 0, fun j => |x j|,
              hqf, ?_, ?_, hbox, hqf0, ?_, ?_⟩
            · intro i j _; linarith [le_max_left (P.ahat i j * |x j| - qf i) 0]
            · intro j; exact ⟨neg_abs_le _, le_abs_self _⟩
            · intro i j _; exact le_max_right _ _
            · intro j; exact abs_nonneg _
          · rintro ⟨q, r, y, hrow, hqr, hxy, hbox, hq0, hr0, hy0⟩
            refine ⟨hbox, ?_⟩
            rintro A ⟨z, hzJ, hzabs, hzsum, hA⟩ i
            simp only [Matrix.mulVec, dotProduct]
            have hexp : ∑ j, A i j * x j = ∑ j, P.abar i j * x j +
                ∑ j ∈ Finset.univ.filter (fun j => (i, j) ∈ P.J), P.ahat i j * z i j * x j := by
              rw [Finset.sum_filter, ← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl (fun j _ => ?_)
              rw [hA]
              by_cases h : (i, j) ∈ P.J
              · rw [if_pos h]; ring
              · rw [if_neg h, hzJ i j h]; ring
            have hzi : ∑ j ∈ Finset.univ.filter (fun j => (i, j) ∈ P.J), |z i j| ≤ P.Γ := by
              refine le_trans ?_ hzsum
              rw [hsplit (fun ij => |z ij.1 ij.2|) (fun ij h => by simp only [hzJ ij.1 ij.2 h, abs_zero])]
              exact Finset.single_le_sum
                (f := fun i' => ∑ j ∈ Finset.univ.filter (fun j => (i', j) ∈ P.J), |z i' j|)
                (fun i' _ => Finset.sum_nonneg (fun j _ => abs_nonneg _)) (Finset.mem_univ i)
            have hterm : ∀ j ∈ Finset.univ.filter (fun j => (i, j) ∈ P.J),
                P.ahat i j * z i j * x j ≤ |z i j| * q i + r i j := by
              intro j hj
              rw [Finset.mem_filter] at hj
              have ha := P.hahat _ hj.2
              have h1 : P.ahat i j * z i j * x j ≤ P.ahat i j * (|z i j| * |x j|) := by
                have := le_abs_self (P.ahat i j * z i j * x j)
                rw [abs_mul, abs_mul, abs_of_nonneg ha] at this; linarith
              have h2 : |x j| ≤ y j := abs_le.2 ⟨by linarith [(hxy j).1], (hxy j).2⟩
              have h3 : P.ahat i j * (|z i j| * |x j|) ≤ |z i j| * (P.ahat i j * y j) := by
                have := mul_le_mul_of_nonneg_left h2 (mul_nonneg ha (abs_nonneg (z i j)))
                linarith
              have h4 : |z i j| * (P.ahat i j * y j) ≤ |z i j| * (q i + r i j) :=
                mul_le_mul_of_nonneg_left (hqr i j hj.2) (abs_nonneg _)
              have h5 : |z i j| * r i j ≤ r i j := by
                have := mul_le_mul_of_nonneg_right (hzabs i j) (hr0 i j hj.2); linarith
              nlinarith
            have hsum := Finset.sum_le_sum hterm
            rw [Finset.sum_add_distrib, ← Finset.sum_mul] at hsum
            have hqΓ : (∑ j ∈ Finset.univ.filter (fun j => (i, j) ∈ P.J), |z i j|) * q i ≤ q i * P.Γ := by
              have := mul_le_mul_of_nonneg_right hzi (hq0 i); linarith
            rw [hexp]
            linarith [hrow i]
        refine ⟨part1, ?_, ?_⟩
        · intro x
          constructor
          · rintro ⟨hx, hopt⟩
            obtain ⟨q, r, y, h⟩ := (part1 x).1 hx
            exact ⟨q, r, y, h, fun x' q' r' y' h' => hopt x' ((part1 x').2 ⟨q', r', y', h'⟩)⟩
          · rintro ⟨q, r, y, h, hopt⟩
            refine ⟨(part1 x).2 ⟨q, r, y, h⟩, fun x' hx' => ?_⟩
            obtain ⟨q', r', y', h'⟩ := (part1 x').1 hx'
            exact hopt x' q' r' y' h'
        · ext v
          simp only [Set.mem_setOf_eq]
          constructor
          · rintro ⟨x, hx, rfl⟩
            obtain ⟨q, r, y, h⟩ := (part1 x).1 hx
            exact ⟨x, q, r, y, h, rfl⟩
          · rintro ⟨x, q, r, y, h, rfl⟩
            exact ⟨x, (part1 x).2 ⟨q, r, y, h⟩, rfl⟩
