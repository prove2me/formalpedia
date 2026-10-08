-- Prove2me | solution 1 for SkutellaCQP.Preempt.lemma_4_2_24
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T08:21:42.128901+00:00
-- url     : https://prove2.me/submissions/c80bf9e9-12d4-4c24-815d-f52c4042b99f

import Mathlib
import Definitions.Def_SkutellaCQP_Preempt_Setting

open MeasureTheory Finset SkutellaCQP.Preempt

private lemma packing {A : Type} [DecidableEq A] (s : Finset A)
    (a b : A → ℝ) (T : ℝ) (hT : 0 ≤ T)
    (ha : ∀ k ∈ s, 0 ≤ a k) (hb : ∀ k ∈ s, b k ≤ T)
    (hlen : ∀ k ∈ s, a k ≤ b k)
    (hd : ∀ j ∈ s, ∀ k ∈ s, j ≠ k → b j ≤ a k ∨ b k ≤ a j) :
    ∑ k ∈ s, (b k - a k) ≤ T := by
  have hdis : Set.PairwiseDisjoint (↑s) (fun k => Set.Ioc (a k) (b k)) := by
    intro j hj k hk hne
    rcases hd j hj k hk hne with h | h
    · exact Set.Ioc_disjoint_Ioc_of_le h
    · exact (Set.Ioc_disjoint_Ioc_of_le h).symm
  have hsub : (⋃ k ∈ s, Set.Ioc (a k) (b k)) ⊆ Set.Ioc 0 T := by
    intro x hx
    obtain ⟨k,hk,hx⟩ := Set.mem_iUnion₂.mp hx
    exact ⟨(ha k hk).trans_lt hx.1, hx.2.trans (hb k hk)⟩
  have hmeasure := measure_mono (μ := volume) hsub
  rw [measure_biUnion_finset hdis (fun _ _ => measurableSet_Ioc),
    Real.volume_Ioc, sub_zero] at hmeasure
  simp only [Real.volume_Ioc] at hmeasure
  rw [← ENNReal.ofReal_sum_of_nonneg (fun k hk => sub_nonneg.mpr (hlen k hk))] at hmeasure
  exact (ENNReal.ofReal_le_ofReal_iff hT).mp hmeasure

private lemma slots_le {m n : ℕ} (r : Fin m → Fin n → ℝ) (i : Fin m)
    (a b : ℝ) (hab : a ≤ b) :
    ∑ k : Fin n, overlapLen a b (SkutellaCQP.RelDates.rho r i k) (slotEnd r i k) ≤ b-a := by
  let I : Fin n → Set ℝ := fun k => match slotEnd r i k with
    | some e => Set.Ioc (SkutellaCQP.RelDates.rho r i k) e
    | none => Set.Ioi (SkutellaCQP.RelDates.rho r i k)
  have hmon : Monotone (SkutellaCQP.RelDates.rho r i) := Tuple.monotone_sort (r i)
  have hdl (k l : Fin n) (hkl : k < l) : Disjoint (I k) (I l) := by
    have hn : k.val + 1 < n := lt_of_le_of_lt (by omega) l.isLt
    have he : SkutellaCQP.RelDates.rho r i ⟨k.val+1,hn⟩ ≤ SkutellaCQP.RelDates.rho r i l :=
      hmon (by change k.val+1 ≤ l.val; omega)
    change Disjoint
      (match slotEnd r i k with | some e => Set.Ioc _ e | none => Set.Ioi _)
      (match slotEnd r i l with | some e => Set.Ioc _ e | none => Set.Ioi _)
    simp only [slotEnd, dif_pos hn]
    split_ifs
    · exact Set.Ioc_disjoint_Ioc_of_le he
    · apply Set.disjoint_left.mpr
      intro z hz hz'
      exact (not_lt_of_ge (hz.2.trans he) hz').elim
  have hd : Set.PairwiseDisjoint (↑(univ : Finset (Fin n))) I := by
    intro k _ l _ hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact hdl k l h
    · exact (hdl l k h).symm
  have he (k : Fin n) :
      volume (Set.Ioc a b ∩ I k) =
      ENNReal.ofReal (overlapLen a b (SkutellaCQP.RelDates.rho r i k) (slotEnd r i k)) := by
    dsimp [I]
    cases slotEnd r i k <;>
      simp [overlapLen, Set.Ioc_inter_Ioc, Set.Ioc_inter_Ioi, Real.volume_Ioc,
        ENNReal.ofReal_max, max_comm]
  have hmeas (k : Fin n) : MeasurableSet (I k) := by
    dsimp [I]
    cases slotEnd r i k <;> simp
  have hd' : Set.PairwiseDisjoint (↑(univ : Finset (Fin n))) (fun k => Set.Ioc a b ∩ I k) :=
    fun k hk l hl hne => (hd hk hl hne).mono Set.inter_subset_right Set.inter_subset_right
  have hb := measure_mono (μ := volume)
    (show (⋃ k ∈ (univ : Finset (Fin n)), Set.Ioc a b ∩ I k) ⊆ Set.Ioc a b from by
      intro x hx
      obtain ⟨k,hk,hx⟩ := Set.mem_iUnion₂.mp hx
      exact hx.1)
  rw [measure_biUnion_finset hd' (fun k _ => measurableSet_Ioc.inter (hmeas k)),
    Real.volume_Ioc] at hb
  simp only [he] at hb
  rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => by
    cases slotEnd r i k <;> exact le_max_left _ _)] at hb
  exact (ENNReal.ofReal_le_ofReal_iff (sub_nonneg.mpr hab)).mp hb

private lemma filter_sum {A : Type} (P : List A) (d : A → Prop) [DecidablePred d] (f : A → ℝ) :
    ((P.filter d).map f).sum =
      ∑ t : Fin P.length, if d (P.get t) then f (P.get t) else 0 := by
  have he : ((P.filter d).map f).sum = (P.map (fun q => if d q then f q else 0)).sum := by
    induction P with
    | nil => simp
    | cons q P ih =>
      by_cases hq : d q <;> simp [hq, ih]
  rw [he]
  conv_lhs => rw [← List.ofFn_get P, List.map_ofFn, List.sum_ofFn]
  rfl

private lemma max_nonneg (l : List ℝ) : 0 ≤ l.foldr max 0 := by
  induction l with
  | nil => rfl
  | cons a l ih => exact ih.trans (le_max_right _ _)

theorem solution {m n : ℕ} (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ) (r : Fin m → Fin n → ℝ)
    (hp : ∀ i j, 0 < p i j) (hw : ∀ j, 0 ≤ w j) (hr : ∀ i j, 0 ≤ r i j)
    (P : PSched m n) (hP : PFeasible p r P) :
    rhs24 p w (frac p r P) ≤ pval w P := by
  unfold rhs24 pval
  apply sum_le_sum
  intro j _
  apply mul_le_mul_of_nonneg_left _ (hw j)
  let J := univ.filter (fun t : Fin P.length => (P.get t).job = j)
  have hs (t : Fin P.length) : 0 ≤ (P.get t).start := by
    have hh := hP.1 (P.get t) (List.get_mem _ _)
    exact (hr _ _).trans hh.1
  have hlen (t : Fin P.length) : (P.get t).start ≤ (P.get t).stop :=
    (hP.1 (P.get t) (List.get_mem _ _)).2
  have hpack : (∑ t ∈ J, ((P.get t).stop - (P.get t).start)) ≤ pcompl P j := by
    apply packing J (fun t => (P.get t).start) (fun t => (P.get t).stop) (pcompl P j)
    · exact max_nonneg _
    · intro t _; exact hs t
    · intro t ht
      apply List.le_max_of_le' 0 _ le_rfl
      apply List.mem_map.mpr
      exact ⟨P.get t, List.mem_filter.mpr ⟨List.get_mem _ _, by simpa [J] using ht⟩, rfl⟩
    · intro t _; exact hlen t
    · intro t ht u hu htu
      apply hP.2.2.1 t u htu
      have ht' : (P.get t).job = j := (mem_filter.mp ht).2
      have hu' : (P.get u).job = j := (mem_filter.mp hu).2
      exact ht'.trans hu'.symm
  have hf (i : Fin m) (k : Fin n) :
      frac p r P i k j * p i j = ∑ t : Fin P.length,
        if (P.get t).job = j ∧ (P.get t).mach = i then
          overlapLen (P.get t).start (P.get t).stop (SkutellaCQP.RelDates.rho r i k) (slotEnd r i k)
        else 0 := by
    unfold frac
    rw [div_mul_cancel₀ _ (ne_of_gt (hp i j))]
    exact filter_sum _ _ _
  simp only [hf]
  have he : (∑ i, ∑ k, ∑ t : Fin P.length,
        if (P.get t).job = j ∧ (P.get t).mach = i then
          overlapLen (P.get t).start (P.get t).stop (SkutellaCQP.RelDates.rho r i k) (slotEnd r i k)
        else 0) = ∑ t : Fin P.length, ∑ i, ∑ k,
        if (P.get t).job = j ∧ (P.get t).mach = i then
          overlapLen (P.get t).start (P.get t).stop (SkutellaCQP.RelDates.rho r i k) (slotEnd r i k)
        else 0 := by
    conv_lhs =>
      arg 2
      ext i
      rw [sum_comm]
    rw [sum_comm]
  rw [he]
  apply le_trans _ hpack
  rw [sum_filter]
  apply sum_le_sum
  intro t _
  by_cases ht : (P.get t).job = j
  · simp only [ht, true_and, sum_ite_irrel, sum_const_zero, sum_ite_eq, mem_univ, if_true]
    exact slots_le r (P.get t).mach _ _ (hlen t)
  · simp only [ht, false_and, if_false, sum_const_zero, le_refl]

#print axioms solution
