-- Prove2me | solution 1 for OnlinePrimalDual.AdAuctions.allocation_competitive_ratio_v2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T01:24:31.650781+00:00
-- url     : https://prove2.me/submissions/16855806-dd9c-4e4e-b70c-3ab9c2c2cacb

import Mathlib
import Definitions.Def_OnlinePrimalDual_AdAuctions_AdAuctionsInstance
import Definitions.Def_OnlinePrimalDual_AdAuctions_cParam
import Definitions.Def_OnlinePrimalDual_AdAuctions_buyerX
import Definitions.Def_OnlinePrimalDual_AdAuctions_revenue
import Definitions.Def_OnlinePrimalDual_AdAuctions_actualCharge
import Definitions.Def_OnlinePrimalDual_AdAuctions_allocRun_v2



namespace OnlinePrimalDual.AdAuctions

lemma pd_c_gt_one {I M : Type*} [Fintype I] [Fintype M]
    (inst : AdAuctionsInstance I M) : 1 < cParam inst := by
  unfold cParam
  apply Real.one_lt_rpow
  · linarith [inst.hRmax_pos]
  · exact one_div_pos.mpr inst.hRmax_pos

lemma pd_bern {I M : Type*} [Fintype I] [Fintype M]
    (inst : AdAuctionsInstance I M) (t : ℝ) (ht0 : 0 ≤ t) (htR : t ≤ inst.Rmax) :
    cParam inst ^ t ≤ 1 + t := by
  have hR := inst.hRmax_pos
  unfold cParam
  rw [← Real.rpow_mul (by linarith)]
  have h1 : 0 ≤ 1 / inst.Rmax * t := by positivity
  have h2 : 1 / inst.Rmax * t ≤ 1 := by
    rw [div_mul_eq_mul_div, one_mul, div_le_one hR]; exact htR
  have := rpow_one_add_le_one_add_mul_self (s := inst.Rmax) (by linarith) h1 h2
  calc (1 + inst.Rmax) ^ (1 / inst.Rmax * t) ≤ 1 + 1 / inst.Rmax * t * inst.Rmax := this
    _ = 1 + t := by field_simp

lemma pd_fold {I M : Type*} [Fintype I] [Fintype M]
    (inst : AdAuctionsInstance I M) (i : I) (l : List ℝ)
    (hl : ∀ bd ∈ l, 0 ≤ bd ∧ bd ≤ inst.Rmax * inst.B i) (x S : ℝ)
    (hx : x ≥ (1 / (cParam inst - 1)) * (cParam inst ^ (S / inst.B i) - 1)) :
    l.foldl (fun x bd => x * (1 + bd / inst.B i) + bd / ((cParam inst - 1) * inst.B i)) x ≥
      (1 / (cParam inst - 1)) * (cParam inst ^ ((S + l.sum) / inst.B i) - 1) := by
  induction l generalizing x S with
  | nil => simpa using hx
  | cons b l ih =>
    simp only [List.foldl_cons, List.sum_cons]
    have hb := hl b (by simp)
    have hl' : ∀ bd ∈ l, 0 ≤ bd ∧ bd ≤ inst.Rmax * inst.B i :=
      fun bd h => hl bd (List.mem_cons_of_mem _ h)
    rw [show S + (b + l.sum) = (S + b) + l.sum by ring]
    apply ih hl'
    have hB := inst.hB_pos i
    have hc := pd_c_gt_one inst
    have hc1 : 0 < cParam inst - 1 := by linarith
    set c := cParam inst with hcdef
    set B := inst.B i
    set t := b / B with htdef
    have ht0 : 0 ≤ t := div_nonneg hb.1 hB.le
    have htR : t ≤ inst.Rmax := by
      rw [htdef, div_le_iff₀ hB]; exact hb.2
    have hbern : c ^ t ≤ 1 + t := pd_bern inst t ht0 htR
    have hsplit : c ^ ((S + b) / B) = c ^ (S / B) * c ^ t := by
      rw [← Real.rpow_add (by linarith)]; congr 1; rw [htdef]; ring
    have hpos : 0 ≤ c ^ (S / B) := Real.rpow_nonneg (by linarith) _
    have hbB : b / ((c - 1) * B) = t / (c - 1) := by
      rw [htdef, div_div, mul_comm B]
    rw [hsplit, hbB]
    have hmono : x * (1 + t) ≥ (1 / (c - 1)) * (c ^ (S / B) - 1) * (1 + t) :=
      mul_le_mul_of_nonneg_right hx (by linarith)
    have key : (1 / (c - 1)) * (c ^ (S / B) - 1) * (1 + t) + t / (c - 1) =
        (1 / (c - 1)) * (c ^ (S / B) * (1 + t) - 1) := by
      field_simp; ring
    have key2 : (1 / (c - 1)) * (c ^ (S / B) * c ^ t - 1) ≤
        (1 / (c - 1)) * (c ^ (S / B) * (1 + t) - 1) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have := mul_le_mul_of_nonneg_left hbern hpos
      linarith
    linarith

lemma pd_dnf {I M : Type*} [Fintype I] [Fintype M]
    (inst : AdAuctionsInstance I M) (l : List ℝ) (i : I)
    (hl : ∀ bd ∈ l, 0 ≤ bd ∧ bd ≤ inst.Rmax * inst.B i) :
    buyerX inst i l ≥
      (1 / (cParam inst - 1)) * (cParam inst ^ (l.sum / inst.B i) - 1) := by
  have h := pd_fold inst i l hl 0 0 (by simp)
  simpa [buyerX] using h

lemma pd_buyerX_append {I M : Type*} [Fintype I] [Fintype M]
    (inst : AdAuctionsInstance I M) (i : I) (l : List ℝ) (bd : ℝ) :
    buyerX inst i (l ++ [bd]) =
      buyerX inst i l * (1 + bd / inst.B i) + bd / ((cParam inst - 1) * inst.B i) := by
  simp [buyerX, List.foldl_append]

lemma pd_buyerX_nonneg {I M : Type*} [Fintype I] [Fintype M]
    (inst : AdAuctionsInstance I M) (i : I) (l : List ℝ) (hl : ∀ bd ∈ l, 0 ≤ bd) :
    0 ≤ buyerX inst i l := by
  have hc := pd_c_gt_one inst
  have hB := inst.hB_pos i
  have key : ∀ (l : List ℝ), (∀ bd ∈ l, 0 ≤ bd) → ∀ x : ℝ, 0 ≤ x →
      0 ≤ l.foldl (fun x bd => x * (1 + bd / inst.B i) + bd / ((cParam inst - 1) * inst.B i)) x := by
    intro l
    induction l with
    | nil => intro _ x hx; simpa using hx
    | cons b l ih =>
      intro hl x hx
      simp only [List.foldl_cons]
      apply ih (fun bd h => hl bd (List.mem_cons_of_mem _ h))
      have hb := hl b (by simp)
      have hc1 : 0 < cParam inst - 1 := by linarith
      have : 0 ≤ b / inst.B i := div_nonneg hb hB.le
      have : 0 ≤ b / ((cParam inst - 1) * inst.B i) := by positivity
      positivity
  exact key l hl 0 le_rfl

variable {I M : Type*} [Fintype I] [Fintype M] [DecidableEq I]

noncomputable def pdStep (inst : AdAuctionsInstance I M) (alloc : M → I) (won : I → List ℝ)
    (j : M) : I → List ℝ :=
  if 1 ≤ buyerX inst (alloc j) (won (alloc j)) then won
  else Function.update won (alloc j) (won (alloc j) ++ [inst.b (alloc j) j])

lemma pd_run_snoc (inst : AdAuctionsInstance I M) (alloc : M → I) (l : List M) (j : M) :
    allocRun inst (l ++ [j]) alloc = pdStep inst alloc (allocRun inst l alloc) j := by
  unfold allocRun pdStep
  rw [List.foldl_append]
  rfl

lemma pd_run_nil (inst : AdAuctionsInstance I M) (alloc : M → I) :
    allocRun inst [] alloc = fun _ => [] := by
  simp [allocRun]

lemma pd_step_inv (inst : AdAuctionsInstance I M) (alloc : M → I) (s : I → List ℝ) (j : M)
    (hs : ∀ i, ∀ bd ∈ s i, 0 ≤ bd ∧ bd ≤ inst.Rmax * inst.B i)
    (hr : ∀ i, (s i).sum ≤ inst.B i * (1 + inst.Rmax)) :
    (∀ i, ∀ bd ∈ pdStep inst alloc s j i, 0 ≤ bd ∧ bd ≤ inst.Rmax * inst.B i) ∧
    (∀ i, (pdStep inst alloc s j i).sum ≤ inst.B i * (1 + inst.Rmax)) := by
  unfold pdStep
  split_ifs with h
  · exact ⟨hs, hr⟩
  · push_neg at h
    set a := alloc j with ha
    have hbj0 := inst.hb_nonneg a j
    have hbj1 := inst.hRmax_bound a j
    have hc := pd_c_gt_one inst
    have hdnf := pd_dnf inst (s a) a (hs a)
    have hBa := inst.hB_pos a
    have hc1 : 0 < cParam inst - 1 := by linarith
    have hlt : (s a).sum < inst.B a := by
      have h1 : cParam inst ^ ((s a).sum / inst.B a) < cParam inst ^ (1 : ℝ) := by
        rw [Real.rpow_one]
        have : (1 / (cParam inst - 1)) * (cParam inst ^ ((s a).sum / inst.B a) - 1) < 1 := by
          linarith
        rw [one_div, inv_mul_lt_iff₀ hc1] at this
        linarith
      rw [Real.rpow_lt_rpow_left_iff hc] at h1
      rwa [div_lt_one hBa] at h1
    constructor
    · intro i bd hbd
      by_cases hi : i = a
      · subst hi
        rw [Function.update_self] at hbd
        rcases List.mem_append.1 hbd with h' | h'
        · exact hs _ bd h'
        · simp at h'; subst h'; exact ⟨hbj0, hbj1⟩
      · rw [Function.update_of_ne hi] at hbd
        exact hs i bd hbd
    · intro i
      by_cases hi : i = a
      · subst hi
        rw [Function.update_self]
        simp only [List.sum_append, List.sum_cons, List.sum_nil, add_zero]
        nlinarith [inst.hRmax_pos]
      · rw [Function.update_of_ne hi]
        exact hr i

lemma pd_inv (inst : AdAuctionsInstance I M) (alloc : M → I) (l : List M) :
    (∀ i, ∀ bd ∈ allocRun inst l alloc i, 0 ≤ bd ∧ bd ≤ inst.Rmax * inst.B i) ∧
    (∀ i, (allocRun inst l alloc i).sum ≤ inst.B i * (1 + inst.Rmax)) := by
  induction l using List.reverseRecOn with
  | nil =>
    rw [pd_run_nil]
    refine ⟨fun i bd h => by simp at h, fun i => ?_⟩
    simp only [List.sum_nil]
    have := inst.hB_pos i; have := inst.hRmax_pos
    positivity
  | append_singleton l j ih =>
    rw [pd_run_snoc]
    exact pd_step_inv inst alloc _ j ih.1 ih.2

lemma pd_step_mono (inst : AdAuctionsInstance I M) (alloc : M → I) (s : I → List ℝ) (j : M)
    (hs : ∀ i, ∀ bd ∈ s i, 0 ≤ bd ∧ bd ≤ inst.Rmax * inst.B i) (i : I) :
    buyerX inst i (s i) ≤ buyerX inst i (pdStep inst alloc s j i) := by
  unfold pdStep
  split_ifs with h
  · exact le_rfl
  · by_cases hi : i = alloc j
    · subst hi
      rw [Function.update_self, pd_buyerX_append]
      have hx := pd_buyerX_nonneg inst (alloc j) (s (alloc j)) (fun bd h => (hs _ bd h).1)
      have hc := pd_c_gt_one inst
      have hB := inst.hB_pos (alloc j)
      have hb := inst.hb_nonneg (alloc j) j
      have hc1 : 0 < cParam inst - 1 := by linarith
      have : 0 ≤ inst.b (alloc j) j / inst.B (alloc j) := div_nonneg hb hB.le
      have : 0 ≤ inst.b (alloc j) j / ((cParam inst - 1) * inst.B (alloc j)) := by positivity
      nlinarith
    · rw [Function.update_of_ne hi]

lemma pd_mono (inst : AdAuctionsInstance I M) (alloc : M → I) (r : List M) :
    ∀ (l : List M) (i : I), buyerX inst i (allocRun inst l alloc i) ≤
      buyerX inst i (allocRun inst (l ++ r) alloc i) := by
  induction r with
  | nil => intro l i; simp
  | cons j r ih =>
    intro l i
    have := ih (l ++ [j]) i
    rw [List.append_assoc, List.singleton_append] at this
    refine le_trans ?_ this
    rw [pd_run_snoc]
    exact pd_step_mono inst alloc _ j (pd_inv inst alloc l).1 i

lemma pd_weak (b : I → M → ℝ) (B X : I → ℝ) (Z : M → ℝ) (y : I → M → ℝ)
    (hy : ∀ i j, 0 ≤ y i j) (hX : ∀ i, 0 ≤ X i) (hZ : ∀ j, 0 ≤ Z j)
    (hfeas : ∀ i j, b i j ≤ b i j * X i + Z j)
    (hy1 : ∀ j, ∑ i, y i j ≤ 1) (hy2 : ∀ i, ∑ j, b i j * y i j ≤ B i) :
    ∑ i, ∑ j, b i j * y i j ≤ ∑ i, B i * X i + ∑ j, Z j := by
  calc ∑ i, ∑ j, b i j * y i j
      ≤ ∑ i, ∑ j, (X i * (b i j * y i j) + Z j * y i j) := by
        apply Finset.sum_le_sum; intro i _
        apply Finset.sum_le_sum; intro j _
        nlinarith [mul_le_mul_of_nonneg_right (hfeas i j) (hy i j)]
    _ = ∑ i, X i * ∑ j, b i j * y i j + ∑ j, Z j * ∑ i, y i j := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
        rw [Finset.sum_comm (f := fun i j => Z j * y i j)]
        simp only [← Finset.mul_sum]
    _ ≤ ∑ i, B i * X i + ∑ j, Z j := by
        apply add_le_add
        · apply Finset.sum_le_sum; intro i _
          nlinarith [hX i, hy2 i]
        · calc ∑ j, Z j * ∑ i, y i j ≤ ∑ j, Z j * 1 := by
                apply Finset.sum_le_sum; intro j _
                exact mul_le_mul_of_nonneg_left (hy1 j) (hZ j)
            _ = ∑ j, Z j := by simp

lemma pd_takeWhile {M : Type*} [DecidableEq M] (l r : List M) (j : M) (h : (l ++ [j] ++ r).Nodup) :
    (l ++ [j] ++ r).takeWhile (· ≠ j) = l := by
  have hj : ∀ a ∈ l, a ≠ j := by
    rw [List.nodup_append] at h
    have := h.1
    simpa using (List.nodup_append.1 this).2.2
  rw [List.append_assoc, List.takeWhile_append]
  have h1 : l.takeWhile (· ≠ j) = l := by
    rw [List.takeWhile_eq_self_iff]; intro a ha; simpa using hj a ha
  rw [h1]
  simp

noncomputable def pdZ [DecidableEq M] (inst : AdAuctionsInstance I M) (ord : List M) (alloc : M → I)
    (j : M) : ℝ :=
  max 0 (inst.b (alloc j) j *
    (1 - buyerX inst (alloc j) (allocRun inst (ord.takeWhile (· ≠ j)) alloc (alloc j))))

lemma pd_potential [DecidableEq M] (inst : AdAuctionsInstance I M) (alloc : M → I) (ord : List M)
    (hnd : ord.Nodup) : ∀ l : List M, l <+: ord →
    ∑ i, inst.B i * buyerX inst i (allocRun inst l alloc i) + (l.map (pdZ inst ord alloc)).sum ≤
      cParam inst / (cParam inst - 1) * ∑ i, (allocRun inst l alloc i).sum := by
  intro l
  induction l using List.reverseRecOn with
  | nil =>
    intro _
    rw [pd_run_nil]
    simp [buyerX]
  | append_singleton l j ih =>
    intro hpre
    have hpre' : l <+: ord := (List.prefix_append l [j]).trans hpre
    have ih := ih hpre'
    obtain ⟨r, hr⟩ := hpre
    have htw : ord.takeWhile (· ≠ j) = l := by
      rw [← hr] at hnd ⊢
      exact pd_takeWhile l r j hnd
    have hz : pdZ inst ord alloc j = max 0 (inst.b (alloc j) j *
        (1 - buyerX inst (alloc j) (allocRun inst l alloc (alloc j)))) := by
      unfold pdZ; rw [htw]
    rw [pd_run_snoc, List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [hz]
    set s := allocRun inst l alloc with hs
    set a := alloc j with ha
    set x := buyerX inst a (s a) with hx
    have hb0 := inst.hb_nonneg a j
    have hc := pd_c_gt_one inst
    have hc1 : 0 < cParam inst - 1 := by linarith
    have hBa := inst.hB_pos a
    by_cases h1 : 1 ≤ x
    · have : max 0 (inst.b a j * (1 - x)) = 0 := by
        apply max_eq_left
        nlinarith
      rw [this]
      unfold pdStep
      rw [if_pos h1]
      linarith
    · push_neg at h1
      have : max 0 (inst.b a j * (1 - x)) = inst.b a j * (1 - x) := by
        apply max_eq_right
        apply mul_nonneg hb0; linarith
      rw [this]
      have hX : ∀ i, inst.B i * buyerX inst i (pdStep inst alloc s j i) =
          inst.B i * buyerX inst i (s i) +
            (if i = a then inst.b a j * x + inst.b a j / (cParam inst - 1) else 0) := by
        intro i
        unfold pdStep
        rw [if_neg (not_le.2 h1)]
        by_cases hi : i = a
        · subst hi
          rw [Function.update_self, pd_buyerX_append, if_pos rfl]
          have : inst.B a ≠ 0 := hBa.ne'
          have : cParam inst - 1 ≠ 0 := hc1.ne'
          field_simp
          ring
        · rw [Function.update_of_ne hi, if_neg hi]; ring
      have hR : ∀ i, (pdStep inst alloc s j i).sum =
          (s i).sum + (if i = a then inst.b a j else 0) := by
        intro i
        unfold pdStep
        rw [if_neg (not_le.2 h1)]
        by_cases hi : i = a
        · subst hi
          rw [Function.update_self, if_pos rfl]
          simp only [List.sum_append, List.sum_cons, List.sum_nil, add_zero]
          rfl
        · rw [Function.update_of_ne hi, if_neg hi]; ring
      simp only [hX, hR, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      have key : inst.b a j * x + inst.b a j / (cParam inst - 1) + inst.b a j * (1 - x) =
          cParam inst / (cParam inst - 1) * inst.b a j := by
        field_simp
        ring
      nlinarith [key]

lemma pd_feas [DecidableEq M] (inst : AdAuctionsInstance I M) (ord : List M) (alloc : M → I)
    (halloc : ∀ j i,
      inst.b i j * (1 - buyerX inst i (allocRun inst (ord.takeWhile (· ≠ j)) alloc i)) ≤
        inst.b (alloc j) j *
          (1 - buyerX inst (alloc j) (allocRun inst (ord.takeWhile (· ≠ j)) alloc (alloc j)))) :
    ∀ i j, inst.b i j ≤ inst.b i j * buyerX inst i (allocRun inst ord alloc i) +
      pdZ inst ord alloc j := by
  intro i j
  have h1 := halloc j i
  have h2 : inst.b i j * (1 - buyerX inst i (allocRun inst (ord.takeWhile (· ≠ j)) alloc i)) ≤
      pdZ inst ord alloc j := le_trans h1 (le_max_right _ _)
  have h3 : buyerX inst i (allocRun inst (ord.takeWhile (· ≠ j)) alloc i) ≤
      buyerX inst i (allocRun inst ord alloc i) := by
    have := pd_mono inst alloc (ord.dropWhile (· ≠ j)) (ord.takeWhile (· ≠ j)) i
    rwa [List.takeWhile_append_dropWhile] at this
  have hb := inst.hb_nonneg i j
  nlinarith [mul_le_mul_of_nonneg_left h3 hb]

theorem H8_core {I M : Type*} [Fintype I] [Fintype M] [DecidableEq I]
    [DecidableEq M] (inst : AdAuctionsInstance I M) (ord : List M) (hord_nodup : ord.Nodup)
    (hord_mem : ∀ j, j ∈ ord) (alloc : M → I)
    (halloc : ∀ j i,
      inst.b i j * (1 - buyerX inst i (allocRun inst (ord.takeWhile (· ≠ j)) alloc i)) ≤
        inst.b (alloc j) j *
          (1 - buyerX inst (alloc j) (allocRun inst (ord.takeWhile (· ≠ j)) alloc (alloc j)))) :
    ∀ y'' : I → M → ℝ, (∀ i j, 0 ≤ y'' i j) →
      (∀ j, ∑ i, y'' i j ≤ 1) →
      (∀ i, ∑ j, inst.b i j * y'' i j ≤ inst.B i) →
      ∑ i, actualCharge inst (allocRun inst ord alloc) i ≥
        (1 - 1 / cParam inst) * (1 - inst.Rmax) *
          (∑ i, ∑ j, inst.b i j * y'' i j) := by
  intro y hy0 hy1 hy2
  obtain ⟨hvalid, hrev⟩ := pd_inv inst alloc ord
  have hc := pd_c_gt_one inst
  have hc1 : 0 < cParam inst - 1 := by linarith
  have hrev0 : ∀ i, 0 ≤ (allocRun inst ord alloc i).sum := fun i =>
    List.sum_nonneg (fun bd h => (hvalid i bd h).1)
  have hx0 : ∀ i, 0 ≤ buyerX inst i (allocRun inst ord alloc i) := fun i =>
    pd_buyerX_nonneg inst i _ (fun bd h => (hvalid i bd h).1)
  have hZ0 : ∀ j, 0 ≤ pdZ inst ord alloc j := fun j => le_max_left _ _
  have hweak := pd_weak inst.b inst.B (fun i => buyerX inst i (allocRun inst ord alloc i))
    (pdZ inst ord alloc) y hy0 hx0 hZ0 (pd_feas inst ord alloc halloc) hy1 hy2
  have hpot := pd_potential inst alloc ord hord_nodup ord (List.prefix_refl _)
  have hZsum : ∑ j, pdZ inst ord alloc j = (ord.map (pdZ inst ord alloc)).sum := by
    have : ord.toFinset = Finset.univ := by
      ext j; simp [hord_mem j]
    rw [← this]
    exact List.sum_toFinset _ hord_nodup
  rw [hZsum] at hweak
  set R := ∑ i, (allocRun inst ord alloc i).sum with hR
  set P := ∑ i, ∑ j, inst.b i j * y i j with hP
  have hR0 : 0 ≤ R := Finset.sum_nonneg (fun i _ => hrev0 i)
  have hPR : (cParam inst - 1) / cParam inst * P ≤ R := by
    have h1 : P ≤ cParam inst / (cParam inst - 1) * R := by linarith
    have : (cParam inst - 1) / cParam inst * P ≤ (cParam inst - 1) / cParam inst *
        (cParam inst / (cParam inst - 1) * R) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have e : (cParam inst - 1) / cParam inst * (cParam inst / (cParam inst - 1) * R) = R := by
      field_simp
    linarith
  have hP0 : 0 ≤ P := Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ =>
    mul_nonneg (inst.hb_nonneg i j) (hy0 i j)))
  have e1 : 1 - 1 / cParam inst = (cParam inst - 1) / cParam inst := by
    field_simp
  rw [ge_iff_le, e1]
  by_cases hR1 : 1 ≤ inst.Rmax
  · have hact : 0 ≤ ∑ i, actualCharge inst (allocRun inst ord alloc) i :=
      Finset.sum_nonneg (fun i _ => le_min (hrev0 i) (inst.hB_pos i).le)
    have : (cParam inst - 1) / cParam inst * (1 - inst.Rmax) * P ≤ 0 := by
      have h0 : 0 ≤ (cParam inst - 1) / cParam inst := by positivity
      have : (cParam inst - 1) / cParam inst * (1 - inst.Rmax) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos h0 (by linarith)
      exact mul_nonpos_of_nonpos_of_nonneg this hP0
    linarith
  · push_neg at hR1
    have hact : ∀ i, (1 - inst.Rmax) * (allocRun inst ord alloc i).sum ≤
        actualCharge inst (allocRun inst ord alloc) i := by
      intro i
      unfold actualCharge revenue
      have hr0 := hrev0 i
      have hrb := hrev i
      have hB := inst.hB_pos i
      have hR0' := inst.hRmax_pos
      rcases le_total ((allocRun inst ord alloc i).sum) (inst.B i) with h | h
      · rw [min_eq_left h]; nlinarith
      · rw [min_eq_right h]
        nlinarith [mul_le_mul_of_nonneg_left hrb (by linarith : (0:ℝ) ≤ 1 - inst.Rmax)]
    have hsum : (1 - inst.Rmax) * R ≤ ∑ i, actualCharge inst (allocRun inst ord alloc) i := by
      rw [hR, Finset.mul_sum]
      exact Finset.sum_le_sum (fun i _ => hact i)
    have : (cParam inst - 1) / cParam inst * (1 - inst.Rmax) * P ≤ (1 - inst.Rmax) * R := by
      have := mul_le_mul_of_nonneg_left hPR (by linarith : (0:ℝ) ≤ 1 - inst.Rmax)
      nlinarith
    linarith

end OnlinePrimalDual.AdAuctions

open OnlinePrimalDual.AdAuctions


theorem solution {I M : Type*} [Fintype I] [Fintype M] [DecidableEq I]
    [DecidableEq M] (inst : AdAuctionsInstance I M) (ord : List M) (hord_nodup : ord.Nodup)
    (hord_mem : ∀ j, j ∈ ord) (alloc : M → I)
    (halloc : ∀ j i,
      inst.b i j * (1 - buyerX inst i (allocRun inst (ord.takeWhile (· ≠ j)) alloc i)) ≤
        inst.b (alloc j) j *
          (1 - buyerX inst (alloc j) (allocRun inst (ord.takeWhile (· ≠ j)) alloc (alloc j)))) :
    ∀ y'' : I → M → ℝ, (∀ i j, 0 ≤ y'' i j) →
      (∀ j, ∑ i, y'' i j ≤ 1) →
      (∀ i, ∑ j, inst.b i j * y'' i j ≤ inst.B i) →
      ∑ i, actualCharge inst (allocRun inst ord alloc) i ≥
        (1 - 1 / cParam inst) * (1 - inst.Rmax) *
          (∑ i, ∑ j, inst.b i j * y'' i j) := by
  exact H8_core inst ord hord_nodup hord_mem alloc halloc
