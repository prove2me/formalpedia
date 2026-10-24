-- Prove2me | solution 1 for UniformPrecSched.Makespan.theorem_3_5
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-24T05:43:49.239978+00:00
-- url     : https://prove2.me/submissions/19e03737-f1bd-4eb1-a276-9a86ea5674a8

import Mathlib
import Definitions.Def_UniformPrecSched_Makespan_Model
import Definitions.Def_UniformPrecSched_Makespan_LP

set_option autoImplicit false

namespace UniformPrecSched.Makespan.C36Aux

open UniformPrecSched.Makespan MeasureTheory

theorem classSpeed_mem {n m : ℕ} (I : Instance n m) (κ : Fin (numSpeeds I)) :
    ∃ i, I.s i = classSpeed I κ := by
  have h : classSpeed I κ ∈ speedSet I := by
    unfold classSpeed; exact Finset.orderEmbOfFin_mem _ _ _
  simp only [speedSet, Finset.mem_image, Finset.mem_univ, true_and] at h
  exact h

theorem classSpeed_pos {n m : ℕ} (I : Instance n m) (κ : Fin (numSpeeds I)) :
    0 < classSpeed I κ := by
  obtain ⟨i, hi⟩ := classSpeed_mem I κ
  rw [← hi]; exact I.s_pos i

theorem classCount_pos {n m : ℕ} (I : Instance n m) (κ : Fin (numSpeeds I)) :
    0 < classCount I κ := by
  obtain ⟨i, hi⟩ := classSpeed_mem I κ
  unfold classCount
  exact Finset.card_pos.mpr ⟨i, by simp [hi]⟩

theorem numSpeeds_pos {n m : ℕ} (I : Instance n m) : 0 < numSpeeds I := by
  unfold numSpeeds
  exact Finset.card_pos.mpr ⟨I.s ⟨0, I.m_pos⟩, by simp [speedSet]⟩

theorem classSpeed_inj {n m : ℕ} (I : Instance n m) {a b : Fin (numSpeeds I)}
    (h : classSpeed I a = classSpeed I b) : a = b := by
  unfold classSpeed at h
  exact Fin.rev_injective (((speedSet I).orderEmbOfFin rfl).injective h)

theorem c_pos {n m : ℕ} (I : Instance n m) (κ : Fin (numSpeeds I)) :
    0 < (classCount I κ : ℝ) * classSpeed I κ :=
  mul_pos (by exact_mod_cast classCount_pos I κ) (classSpeed_pos I κ)

/-! ### Chain bound (Lemma 3.3 shape, threshold `γ`) -/

theorem pbar_pos {n m : ℕ} (I : Instance n m) (x : Fin (numSpeeds I) → Fin n → ℝ)
    (C : Fin n → ℝ) (D : ℝ) (hLP : LPFeasible I x C D) (j : Fin n) :
    0 < pbar I x j := by
  obtain ⟨h1, -, -, -, -, h8⟩ := hLP
  have hex : ∃ κ, 0 < x κ j := by
    by_contra hcon
    push_neg at hcon
    have : ∑ κ, x κ j ≤ 0 := Finset.sum_nonpos (fun κ _ => hcon κ)
    rw [h1 j] at this; norm_num at this
  obtain ⟨κ0, hκ0⟩ := hex
  unfold pbar
  apply Finset.sum_pos'
  · intro κ _
    exact mul_nonneg (div_nonneg (I.p_pos j).le (classSpeed_pos I κ).le) (h8 κ j)
  · exact ⟨κ0, Finset.mem_univ _,
      mul_pos (div_pos (I.p_pos j) (classSpeed_pos I κ0)) hκ0⟩

theorem chain_sum {n m : ℕ} (I : Instance n m) (x : Fin (numSpeeds I) → Fin n → ℝ)
    (C : Fin n → ℝ) (D : ℝ) (hLP : LPFeasible I x C D) :
    ∀ (N : ℕ) (c : Finset (Fin n)), c.card = N → IsJobChain I c → c.Nonempty →
      ∃ t ∈ c, ∑ j ∈ c, pbar I x j ≤ C t := by
  have hpos := pbar_pos I x C D hLP
  obtain ⟨-, -, h3, h4, -, -⟩ := hLP
  intro N
  induction N with
  | zero =>
    intro c hc _ hne
    exact absurd (Finset.card_pos.mpr hne) (by omega)
  | succ N ih =>
    intro c hc hch hne
    obtain ⟨t, ht, hmax⟩ := Finset.exists_max_image c C hne
    have hbelow : ∀ j ∈ c.erase t, I.prec j t := by
      intro j hj
      have hjt : j ≠ t := Finset.ne_of_mem_erase hj
      have hjc : j ∈ c := Finset.mem_of_mem_erase hj
      rcases hch hjc ht hjt with h | h
      · exact h
      · exfalso
        have := h4 t j h
        have hj := hmax j hjc
        have hp := hpos j
        change pbar I x j ≤ C j - C t at this
        linarith
    have hsum : ∑ j ∈ c, pbar I x j = pbar I x t + ∑ j ∈ c.erase t, pbar I x j :=
      (Finset.add_sum_erase c _ ht).symm
    refine ⟨t, ht, ?_⟩
    rw [hsum]
    rcases (c.erase t).eq_empty_or_nonempty with he | he
    · rw [he, Finset.sum_empty, add_zero]
      exact h3 t
    · have hcard : (c.erase t).card = N := by
        rw [Finset.card_erase_of_mem ht, hc]; rfl
      have hch' : IsJobChain I (c.erase t) := by
        unfold IsJobChain at hch ⊢
        exact hch.mono (by intro y hy; exact Finset.mem_of_mem_erase hy)
      obtain ⟨t', ht', hle⟩ := ih (c.erase t) hcard hch' he
      have := h4 t' t (hbelow t' ht')
      change pbar I x t ≤ C t - C t' at this
      linarith

theorem D_nonneg {n m : ℕ} (I : Instance n m) (x : Fin (numSpeeds I) → Fin n → ℝ)
    (C : Fin n → ℝ) (D : ℝ) (hLP : LPFeasible I x C D) : 0 ≤ D := by
  obtain ⟨-, h2, -, -, -, h8⟩ := hLP
  have h := h2 ⟨0, numSpeeds_pos I⟩
  refine le_trans ?_ h
  apply mul_nonneg
  · apply div_nonneg zero_le_one
    exact mul_nonneg (Nat.cast_nonneg _) (classSpeed_pos I _).le
  · exact Finset.sum_nonneg (fun j _ => mul_nonneg (I.p_pos j).le (h8 _ j))

theorem chain_bound {n m : ℕ} (I : Instance n m) (x : Fin (numSpeeds I) → Fin n → ℝ)
    (C : Fin n → ℝ) (D : ℝ) (hLP : LPFeasible I x C D) (γ : ℝ) (hγ : 0 ≤ γ)
    (k : Assignment I) (hk : IsLPAssignment I x γ k) (c : Finset (Fin n))
    (hc : IsJobChain I c) : chainLength I k c ≤ γ * D := by
  have hD := D_nonneg I x C D hLP
  have hterm : ∀ j ∈ c, I.p j / classSpeed I (k j) ≤ γ * pbar I x j := by
    intro j _
    have h := (hk j).1
    simp only [badSet, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at h
    exact h
  have hle : chainLength I k c ≤ γ * ∑ j ∈ c, pbar I x j := by
    unfold chainLength
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hterm
  rcases c.eq_empty_or_nonempty with he | he
  · subst he
    simp only [chainLength, Finset.sum_empty]
    exact mul_nonneg hγ hD
  · obtain ⟨t, _, hsum⟩ := chain_sum I x C D hLP c.card c rfl hc he
    have h5 := hLP.2.2.2.2.1 t
    have : γ * ∑ j ∈ c, pbar I x j ≤ γ * D :=
      mul_le_mul_of_nonneg_left (le_trans hsum h5) hγ
    linarith

/-! ### Load bound (Lemma 3.4 shape, threshold `γ`) -/

theorem key {n m : ℕ} (I : Instance n m) (x : Fin (numSpeeds I) → Fin n → ℝ)
    (C : Fin n → ℝ) (D : ℝ) (hLP : LPFeasible I x C D) (γ : ℝ) (hγ : 0 ≤ γ)
    (k : Assignment I) (hk : IsLPAssignment I x γ k) (j : Fin n) :
    (γ - 1) * (I.p j * (1 / ((classCount I (k j) : ℝ) * classSpeed I (k j)))) ≤
      γ * ∑ κ, (1 / ((classCount I κ : ℝ) * classSpeed I κ)) * (I.p j * x κ j) := by
  have hpbar := pbar_pos I x C D hLP j
  obtain ⟨h1, -, -, -, -, h8⟩ := hLP
  set B := badSet I x γ j with hBdef
  have hpj := I.p_pos j
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin (numSpeeds I)))
    (fun κ => κ ∈ B) (fun κ => x κ j)
  have hBle : γ * pbar I x j * ∑ κ ∈ Finset.univ.filter (fun κ => κ ∈ B), x κ j ≤ pbar I x j := by
    rw [Finset.mul_sum]
    calc ∑ κ ∈ Finset.univ.filter (fun κ => κ ∈ B), γ * pbar I x j * x κ j
        ≤ ∑ κ ∈ Finset.univ.filter (fun κ => κ ∈ B), I.p j / classSpeed I κ * x κ j := by
          apply Finset.sum_le_sum
          intro κ hκ
          have hm : κ ∈ B := (Finset.mem_filter.mp hκ).2
          have : γ * pbar I x j < I.p j / classSpeed I κ := by
            simpa [hBdef, badSet] using hm
          exact mul_le_mul_of_nonneg_right this.le (h8 κ j)
      _ ≤ ∑ κ, I.p j / classSpeed I κ * x κ j := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          intro κ _ _
          exact mul_nonneg (div_nonneg hpj.le (classSpeed_pos I κ).le) (h8 κ j)
      _ = pbar I x j := rfl
  set SB := ∑ κ ∈ Finset.univ.filter (fun κ => κ ∈ B), x κ j
  set SG := ∑ κ ∈ Finset.univ.filter (fun κ => ¬ κ ∈ B), x κ j
  have hSB : γ * SB ≤ 1 := by
    have : pbar I x j * (γ * SB) ≤ pbar I x j * 1 := by nlinarith
    exact le_of_mul_le_mul_left this hpbar
  have hSG : γ - 1 ≤ γ * SG := by
    have : SB + SG = 1 := by rw [hsplit]; exact h1 j
    nlinarith
  have hck := c_pos I (k j)
  set q := I.p j * (1 / ((classCount I (k j) : ℝ) * classSpeed I (k j))) with hqdef
  have hq : 0 ≤ q := mul_nonneg hpj.le (by positivity)
  calc (γ - 1) * q
      ≤ γ * (SG * q) := by nlinarith
    _ = γ * ∑ κ ∈ Finset.univ.filter (fun κ => ¬ κ ∈ B), x κ j * q := by
        rw [Finset.sum_mul]
    _ ≤ γ * ∑ κ ∈ Finset.univ.filter (fun κ => ¬ κ ∈ B),
          (1 / ((classCount I κ : ℝ) * classSpeed I κ)) * (I.p j * x κ j) := by
        apply mul_le_mul_of_nonneg_left _ hγ
        apply Finset.sum_le_sum
        intro κ hκ
        have hnot : κ ∉ badSet I x γ j := (Finset.mem_filter.mp hκ).2
        have hle := (hk j).2 κ hnot
        have hcκ := c_pos I κ
        have hle' : (classCount I κ : ℝ) * classSpeed I κ ≤
            (classCount I (k j) : ℝ) * classSpeed I (k j) := by
          rw [mul_comm (classCount I κ : ℝ), mul_comm (classCount I (k j) : ℝ)]; exact hle
        have hinv : 1 / ((classCount I (k j) : ℝ) * classSpeed I (k j)) ≤
            1 / ((classCount I κ : ℝ) * classSpeed I κ) :=
          one_div_le_one_div_of_le hcκ hle'
        have hx := h8 κ j
        have : 0 ≤ I.p j * x κ j := mul_nonneg hpj.le hx
        rw [hqdef]
        nlinarith
    _ ≤ γ * ∑ κ, (1 / ((classCount I κ : ℝ) * classSpeed I κ)) * (I.p j * x κ j) := by
        apply mul_le_mul_of_nonneg_left _ hγ
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro κ _ _
        exact mul_nonneg (by have := c_pos I κ; positivity) (mul_nonneg hpj.le (h8 κ j))

theorem load_sum {n m : ℕ} (I : Instance n m) (k : Assignment I) :
    ∑ κ, classLoad I k κ =
      ∑ j, I.p j * (1 / ((classCount I (k j) : ℝ) * classSpeed I (k j))) := by
  rw [← Finset.sum_fiberwise Finset.univ k
    (fun j => I.p j * (1 / ((classCount I (k j) : ℝ) * classSpeed I (k j))))]
  apply Finset.sum_congr rfl
  intro κ _
  unfold classLoad
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [(Finset.mem_filter.mp hj).2]
  have := classSpeed_pos I κ
  have := classCount_pos I κ
  field_simp

theorem load_bound {n m : ℕ} (I : Instance n m) (x : Fin (numSpeeds I) → Fin n → ℝ)
    (C : Fin n → ℝ) (D : ℝ) (hLP : LPFeasible I x C D) (γ : ℝ) (hγ : 0 ≤ γ)
    (k : Assignment I) (hk : IsLPAssignment I x γ k) :
    (γ - 1) * ∑ κ, classLoad I k κ ≤ γ * (numSpeeds I : ℝ) * D := by
  rw [load_sum, Finset.mul_sum]
  have h2 := hLP.2.1
  calc ∑ j, (γ - 1) * (I.p j * (1 / ((classCount I (k j) : ℝ) * classSpeed I (k j))))
      ≤ ∑ j, γ * ∑ κ, (1 / ((classCount I κ : ℝ) * classSpeed I κ)) * (I.p j * x κ j) :=
        Finset.sum_le_sum (fun j _ => key I x C D hLP γ hγ k hk j)
    _ = γ * ∑ κ, (1 / ((classCount I κ : ℝ) * classSpeed I κ)) * ∑ j, I.p j * x κ j := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        simp_rw [Finset.mul_sum]
    _ ≤ γ * ∑ _κ : Fin (numSpeeds I), D := by
        gcongr with κ
        exact h2 κ
    _ = γ * (numSpeeds I : ℝ) * D := by
        simp [Finset.sum_const, Finset.card_univ]; ring

/-! ### Graham-type bound (Theorem 2.1 shape) -/

/-- Times at which every machine of speed class `κ` is busy. -/
noncomputable def busySet {n m : ℕ} (I : Instance n m) (σ : Schedule I)
    (κ : Fin (numSpeeds I)) : Set ℝ :=
  ⋂ i ∈ (Finset.univ.filter fun i => I.s i = classSpeed I κ),
    ⋃ j' ∈ (Finset.univ.filter fun j' => σ.μ j' = i), Set.Ico (σ.S j') (σ.C j')

theorem busySet_meas {n m : ℕ} (I : Instance n m) (σ : Schedule I)
    (κ : Fin (numSpeeds I)) : MeasurableSet (busySet I σ κ) := by
  unfold busySet
  exact Finset.measurableSet_biInter _
    (fun i _ => Finset.measurableSet_biUnion _ (fun j _ => measurableSet_Ico))

theorem mem_busySet {n m : ℕ} (I : Instance n m) (σ : Schedule I)
    (κ : Fin (numSpeeds I)) (t : ℝ) :
    t ∈ busySet I σ κ ↔ ∀ i, I.s i = classSpeed I κ →
      ∃ j', σ.μ j' = i ∧ σ.S j' ≤ t ∧ t < σ.C j' := by
  simp only [busySet, Set.mem_iInter, Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ,
    true_and, Set.mem_Ico, exists_prop]

theorem len_eq {n m : ℕ} (I : Instance n m) (k : Assignment I) (σ : Schedule I)
    (hσ : IsSpeedListSchedule I k σ) (j : Fin n) :
    σ.C j - σ.S j = I.p j / classSpeed I (k j) := by
  unfold Schedule.C
  rw [hσ.1 j]; ring

theorem count_le {n m : ℕ} (I : Instance n m) (k : Assignment I) (σ : Schedule I)
    (hσ : IsSpeedListSchedule I k σ) (κ : Fin (numSpeeds I)) (t : ℝ)
    (ht : t ∈ busySet I σ κ) :
    classCount I κ ≤ ((Finset.univ.filter fun j => k j = κ).filter
      fun j => σ.S j ≤ t ∧ t < σ.C j).card := by
  rw [mem_busySet] at ht
  unfold classCount
  calc (Finset.univ.filter fun i => I.s i = classSpeed I κ).card
      ≤ (((Finset.univ.filter fun j => k j = κ).filter
          fun j => σ.S j ≤ t ∧ t < σ.C j).image σ.μ).card := by
        apply Finset.card_le_card
        intro i hi
        have hi' : I.s i = classSpeed I κ := (Finset.mem_filter.mp hi).2
        obtain ⟨j', hμ, h1, h2⟩ := ht i hi'
        rw [Finset.mem_image]
        refine ⟨j', ?_, hμ⟩
        have hkj : k j' = κ := by
          apply classSpeed_inj
          rw [← hσ.1 j', hμ, hi']
        simp [hkj, h1, h2]
    _ ≤ _ := Finset.card_image_le

theorem vol_busy_le {n m : ℕ} (I : Instance n m) (k : Assignment I) (σ : Schedule I)
    (hσ : IsSpeedListSchedule I k σ) (κ : Fin (numSpeeds I)) :
    volume (busySet I σ κ) ≤ ENNReal.ofReal (classLoad I k κ) := by
  have hmeas := busySet_meas I σ κ
  have hm : (0 : ℝ) < classCount I κ := by exact_mod_cast classCount_pos I κ
  set F := Finset.univ.filter fun j => k j = κ with hF
  have hpt : ∀ t, (classCount I κ : ENNReal) * (busySet I σ κ).indicator 1 t ≤
      ∑ j ∈ F, (Set.Ico (σ.S j) (σ.C j)).indicator 1 t := by
    intro t
    by_cases ht : t ∈ busySet I σ κ
    · rw [Set.indicator_of_mem ht, Pi.one_apply, mul_one]
      simp only [Set.indicator_apply, Pi.one_apply, Set.mem_Ico]
      rw [Finset.sum_boole]
      exact_mod_cast count_le I k σ hσ κ t ht
    · rw [Set.indicator_of_notMem ht, mul_zero]
      exact bot_le
  have hkey : (classCount I κ : ENNReal) * volume (busySet I σ κ) ≤
      ENNReal.ofReal ((classCount I κ : ℝ) * classLoad I k κ) := by
    calc (classCount I κ : ENNReal) * volume (busySet I σ κ)
        = ∫⁻ t, (classCount I κ : ENNReal) * (busySet I σ κ).indicator 1 t := by
          rw [lintegral_const_mul _ (measurable_one.indicator hmeas),
            lintegral_indicator_one hmeas]
      _ ≤ ∫⁻ t, ∑ j ∈ F, (Set.Ico (σ.S j) (σ.C j)).indicator 1 t := lintegral_mono hpt
      _ = ∑ j ∈ F, ∫⁻ t, (Set.Ico (σ.S j) (σ.C j)).indicator 1 t :=
          lintegral_finsetSum _ (fun j _ => measurable_one.indicator measurableSet_Ico)
      _ = ∑ j ∈ F, ENNReal.ofReal (I.p j / classSpeed I κ) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [lintegral_indicator_one measurableSet_Ico, Real.volume_Ico, len_eq I k σ hσ j,
            (Finset.mem_filter.mp hj).2]
      _ = ENNReal.ofReal (∑ j ∈ F, I.p j / classSpeed I κ) := by
          rw [ENNReal.ofReal_sum_of_nonneg]
          intro j _
          exact (div_pos (I.p_pos j) (classSpeed_pos I κ)).le
      _ = ENNReal.ofReal ((classCount I κ : ℝ) * classLoad I k κ) := by
          congr 1
          unfold classLoad
          rw [← hF]
          field_simp
  have hL : 0 ≤ classLoad I k κ := by
    unfold classLoad
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun j _ =>
      (div_pos (I.p_pos j) (classSpeed_pos I κ)).le)
  rw [ENNReal.ofReal_mul hm.le, ENNReal.ofReal_natCast] at hkey
  have h0 : (classCount I κ : ENNReal) ≠ 0 := by
    have := classCount_pos I κ
    exact_mod_cast this.ne'
  exact (ENNReal.mul_le_mul_iff_right h0 (ENNReal.natCast_ne_top _)).mp hkey

theorem cover {n m : ℕ} (I : Instance n m) (k : Assignment I) (σ : Schedule I)
    (hσ : IsSpeedListSchedule I k σ) (j : Fin n) :
    ∃ c : Finset (Fin n), IsJobChain I c ∧ (∀ j' ∈ c, j' = j ∨ I.prec j' j) ∧
      ∀ t, 0 ≤ t → t < σ.C j →
        (∃ κ, t ∈ busySet I σ κ) ∨ ∃ j' ∈ c, t ∈ Set.Ico (σ.S j') (σ.C j') := by
  classical
  have : IsTrans (Fin n) I.prec := ⟨I.prec_trans⟩
  have : IsIrrefl (Fin n) I.prec := ⟨I.prec_irrefl⟩
  have wf : WellFounded I.prec := Finite.wellFounded_of_trans_of_irrefl _
  induction j using wf.induction with
  | _ j ih =>
  have hbusy : ∀ t, 0 ≤ t → (∀ j', I.prec j' j → σ.C j' ≤ t) → t < σ.S j →
      t ∈ busySet I σ (k j) := by
    intro t ht hpre hlt
    rw [mem_busySet]
    intro i hi
    exact hσ.2 t i j ht hi hpre hlt
  obtain ⟨c0, hc0ch, hc0pre, hc0cov⟩ : ∃ c0 : Finset (Fin n), IsJobChain I c0 ∧
      (∀ j' ∈ c0, I.prec j' j) ∧ ∀ t, 0 ≤ t → t < σ.S j →
        (∃ κ, t ∈ busySet I σ κ) ∨ ∃ j' ∈ c0, t ∈ Set.Ico (σ.S j') (σ.C j') := by
    by_cases hP : (Finset.univ.filter fun j' => I.prec j' j).Nonempty
    · obtain ⟨j0, hj0, hmax⟩ := Finset.exists_max_image _ σ.C hP
      have hj0' : I.prec j0 j := (Finset.mem_filter.mp hj0).2
      obtain ⟨c1, hc1ch, hc1pre, hc1cov⟩ := ih j0 hj0'
      refine ⟨c1, hc1ch, ?_, ?_⟩
      · intro j' hj'
        rcases hc1pre j' hj' with h | h
        · rw [h]; exact hj0'
        · exact I.prec_trans _ _ _ h hj0'
      · intro t ht hlt
        by_cases hlt0 : t < σ.C j0
        · exact hc1cov t ht hlt0
        · left
          refine ⟨k j, hbusy t ht (fun j' hj' => ?_) hlt⟩
          exact le_trans (hmax j' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj'⟩))
            (not_lt.mp hlt0)
    · refine ⟨∅, ?_, by simp, ?_⟩
      · simp [IsJobChain]
      · intro t ht hlt
        left
        refine ⟨k j, hbusy t ht ?_ hlt⟩
        intro j' hj'
        exact absurd ⟨j', Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj'⟩⟩ hP
  refine ⟨insert j c0, ?_, ?_, ?_⟩
  · unfold IsJobChain at hc0ch ⊢
    rw [Finset.coe_insert]
    exact hc0ch.insert (fun b hb _ => Or.inr (hc0pre b hb))
  · intro j' hj'
    rcases Finset.mem_insert.mp hj' with h | h
    · exact Or.inl h
    · exact Or.inr (hc0pre j' h)
  · intro t ht hlt
    by_cases hS : σ.S j ≤ t
    · right; exact ⟨j, Finset.mem_insert_self _ _, hS, hlt⟩
    · rcases hc0cov t ht (not_le.mp hS) with h | ⟨j', hj', hmem⟩
      · left; exact h
      · right; exact ⟨j', Finset.mem_insert_of_mem hj', hmem⟩

theorem classLoad_nonneg {n m : ℕ} (I : Instance n m) (k : Assignment I)
    (κ : Fin (numSpeeds I)) : 0 ≤ classLoad I k κ := by
  unfold classLoad
  have := classCount_pos I κ
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun j _ =>
    (div_pos (I.p_pos j) (classSpeed_pos I κ)).le)

theorem chainLength_nonneg {n m : ℕ} (I : Instance n m) (k : Assignment I)
    (c : Finset (Fin n)) : 0 ≤ chainLength I k c := by
  unfold chainLength
  exact Finset.sum_nonneg fun j _ => (div_pos (I.p_pos j) (classSpeed_pos I (k j))).le

theorem graham {n m : ℕ} (I : Instance n m) (k : Assignment I) (σ : Schedule I)
    (hσ : IsSpeedListSchedule I k σ) (j : Fin n) :
    ∃ c, IsJobChain I c ∧ σ.C j ≤ ∑ κ, classLoad I k κ + chainLength I k c := by
  obtain ⟨c, hch, -, hcov⟩ := cover I k σ hσ j
  refine ⟨c, hch, ?_⟩
  have hsub : Set.Ico 0 (σ.C j) ⊆ (⋃ κ ∈ (Finset.univ : Finset (Fin (numSpeeds I))),
      busySet I σ κ) ∪ ⋃ j' ∈ c, Set.Ico (σ.S j') (σ.C j') := by
    intro t ht
    rcases hcov t ht.1 ht.2 with ⟨κ, hκ⟩ | ⟨j', hj', hm⟩
    · exact Or.inl (Set.mem_iUnion₂.mpr ⟨κ, Finset.mem_univ _, hκ⟩)
    · exact Or.inr (Set.mem_iUnion₂.mpr ⟨j', hj', hm⟩)
  have hR : 0 ≤ ∑ κ, classLoad I k κ + chainLength I k c :=
    add_nonneg (Finset.sum_nonneg fun κ _ => classLoad_nonneg I k κ) (chainLength_nonneg I k c)
  have hvol : ENNReal.ofReal (σ.C j) ≤
      ENNReal.ofReal (∑ κ, classLoad I k κ + chainLength I k c) := by
    calc ENNReal.ofReal (σ.C j) = volume (Set.Ico 0 (σ.C j)) := by
          rw [Real.volume_Ico, sub_zero]
      _ ≤ volume ((⋃ κ ∈ (Finset.univ : Finset (Fin (numSpeeds I))),
          busySet I σ κ) ∪ ⋃ j' ∈ c, Set.Ico (σ.S j') (σ.C j')) := measure_mono hsub
      _ ≤ volume (⋃ κ ∈ (Finset.univ : Finset (Fin (numSpeeds I))), busySet I σ κ) +
          volume (⋃ j' ∈ c, Set.Ico (σ.S j') (σ.C j')) := measure_union_le _ _
      _ ≤ ∑ κ, volume (busySet I σ κ) + ∑ j' ∈ c, volume (Set.Ico (σ.S j') (σ.C j')) :=
          add_le_add (measure_biUnion_finset_le _ _) (measure_biUnion_finset_le _ _)
      _ ≤ ∑ κ, ENNReal.ofReal (classLoad I k κ) +
          ∑ j' ∈ c, ENNReal.ofReal (I.p j' / classSpeed I (k j')) := by
          apply add_le_add (Finset.sum_le_sum fun κ _ => vol_busy_le I k σ hσ κ)
          apply le_of_eq
          apply Finset.sum_congr rfl
          intro j' _
          rw [Real.volume_Ico, len_eq I k σ hσ j']
      _ = ENNReal.ofReal (∑ κ, classLoad I k κ + chainLength I k c) := by
          rw [ENNReal.ofReal_add (Finset.sum_nonneg fun κ _ => classLoad_nonneg I k κ)
            (chainLength_nonneg I k c), ENNReal.ofReal_sum_of_nonneg
            (fun κ _ => classLoad_nonneg I k κ), chainLength, ENNReal.ofReal_sum_of_nonneg
            (fun j' _ => (div_pos (I.p_pos j') (classSpeed_pos I (k j'))).le)]
  exact (ENNReal.ofReal_le_ofReal_iff hR).mp hvol

end UniformPrecSched.Makespan.C36Aux

open UniformPrecSched.Makespan in
theorem T35Aux.cor36 {n m : ℕ} (I : Instance n m) (x : Fin (numSpeeds I) → Fin n → ℝ)
    (C : Fin n → ℝ) (D : ℝ) (hLP : LPOptimal I x C D) (k : Assignment I)
    (hk : IsLPAssignment I x (Real.sqrt (numSpeeds I) + 1) k) (σ : Schedule I)
    (hσ : IsSpeedListSchedule I k σ) :
    σ.makespan ≤ ((numSpeeds I : ℝ) + 2 * Real.sqrt (numSpeeds I) + 1) * D := by
  have hF := hLP.1
  have hD := C36Aux.D_nonneg I x C D hF
  set K : ℝ := (numSpeeds I : ℝ) with hKdef
  set s := Real.sqrt K with hsdef
  have hK1 : (1 : ℝ) ≤ K := by
    rw [hKdef]; exact_mod_cast C36Aux.numSpeeds_pos I
  have hs1 : 1 ≤ s := by rw [hsdef]; exact Real.one_le_sqrt.mpr hK1
  have hss : s * s = K := Real.mul_self_sqrt (by linarith)
  have hγ : (0 : ℝ) ≤ s + 1 := by linarith
  have hload := C36Aux.load_bound I x C D hF (s + 1) hγ k hk
  have hL : ∑ κ, classLoad I k κ ≤ (K + s) * D := by
    have h1 : s * ∑ κ, classLoad I k κ ≤ s * ((K + s) * D) := by
      have : (s + 1 - 1) * ∑ κ, classLoad I k κ ≤ (s + 1) * K * D := hload
      have e : s * ((K + s) * D) = (s + 1) * K * D := by rw [← hss]; ring
      rw [e]; simpa using this
    exact le_of_mul_le_mul_left h1 (by linarith)
  have hRHS : 0 ≤ (K + 2 * s + 1) * D := mul_nonneg (by linarith) hD
  unfold Schedule.makespan
  split_ifs with hne
  · obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_sup' hne σ.C
    rw [hj]
    obtain ⟨c, hch, hle⟩ := C36Aux.graham I k σ hσ j
    have hc := C36Aux.chain_bound I x C D hF (s + 1) hγ k hk c hch
    nlinarith
  · exact hRHS

open UniformPrecSched.Makespan in
theorem LPLB.classSpeed_mem {n m : ℕ} (I : Instance n m) (κ : Fin (numSpeeds I)) :
    ∃ i, I.s i = classSpeed I κ := by
  have h : classSpeed I κ ∈ speedSet I := Finset.orderEmbOfFin_mem _ _ _
  simpa [speedSet] using h

open UniformPrecSched.Makespan in
theorem LPLB.classSpeed_pos {n m : ℕ} (I : Instance n m) (κ : Fin (numSpeeds I)) :
    0 < classSpeed I κ := by
  obtain ⟨i, hi⟩ := LPLB.classSpeed_mem I κ
  rw [← hi]; exact I.s_pos i

open UniformPrecSched.Makespan in
theorem LPLB.classCount_pos {n m : ℕ} (I : Instance n m) (κ : Fin (numSpeeds I)) :
    0 < classCount I κ := by
  obtain ⟨i, hi⟩ := LPLB.classSpeed_mem I κ
  unfold classCount
  exact Finset.card_pos.mpr ⟨i, by simp [hi]⟩

open UniformPrecSched.Makespan in
theorem LPLB.numSpeeds_pos {n m : ℕ} (I : Instance n m) : 0 < numSpeeds I := by
  unfold numSpeeds
  exact Finset.card_pos.mpr ⟨I.s ⟨0, I.m_pos⟩, by simp [speedSet]⟩

open UniformPrecSched.Makespan in
theorem LPLB.exists_class {n m : ℕ} (I : Instance n m) (i : Fin m) :
    ∃ κ, classSpeed I κ = I.s i := by
  have h : I.s i ∈ Set.range ((speedSet I).orderEmbOfFin
      (rfl : (speedSet I).card = numSpeeds I)) := by
    rw [Finset.range_orderEmbOfFin]; simp [speedSet]
  obtain ⟨κ', hκ'⟩ := h
  exact ⟨Fin.rev κ', (congrArg ((speedSet I).orderEmbOfFin rfl) (Fin.rev_rev κ')).trans hκ'⟩

open UniformPrecSched.Makespan in
theorem LPLB.le_makespan {n m : ℕ} {I : Instance n m} (σ : Schedule I) (j : Fin n) :
    σ.C j ≤ σ.makespan := by
  unfold Schedule.makespan
  split_ifs with h
  · exact Finset.le_sup' σ.C (Finset.mem_univ j)
  · exact absurd ⟨j, Finset.mem_univ j⟩ h

open UniformPrecSched.Makespan in
theorem LPLB.makespan_nonneg {n m : ℕ} {I : Instance n m} (σ : Schedule I) :
    0 ≤ σ.makespan := by
  unfold Schedule.makespan
  split_ifs with h
  · obtain ⟨j, _⟩ := h
    refine le_trans ?_ (Finset.le_sup' σ.C (Finset.mem_univ j))
    unfold Schedule.C
    have h1 := σ.S_nonneg j
    have h2 := div_pos (I.p_pos j) (I.s_pos (σ.μ j))
    linarith
  · exact le_rfl

open UniformPrecSched.Makespan in
/-- Jobs on one machine occupy disjoint intervals inside `[0, C_max]`, so their total
processing time is at most `C_max`. -/
theorem LPLB.machine_load {n m : ℕ} {I : Instance n m} (σ : Schedule I) (i : Fin m) :
    ∑ j ∈ Finset.univ.filter (fun j => σ.μ j = i), I.p j / I.s (σ.μ j) ≤ σ.makespan := by
  classical
  have key : ∀ T : Finset (Fin n), (∀ j ∈ T, σ.μ j = i) → ∀ M : ℝ, 0 ≤ M →
      (∀ j ∈ T, σ.C j ≤ M) → ∑ j ∈ T, I.p j / I.s (σ.μ j) ≤ M := by
    intro T
    refine Finset.induction_on_max_value (motive := fun T : Finset (Fin n) =>
      (∀ j ∈ T, σ.μ j = i) → ∀ M : ℝ, 0 ≤ M →
      (∀ j ∈ T, σ.C j ≤ M) → ∑ j ∈ T, I.p j / I.s (σ.μ j) ≤ M) σ.S T ?_ ?_
    · intro _ M hM _
      simpa using hM
    · intro a T haT hmax ih hT M hM hC
      have hLa : 0 < I.p a / I.s (σ.μ a) := div_pos (I.p_pos a) (I.s_pos _)
      have hmu : ∀ l ∈ T, σ.μ l = σ.μ a := fun l hl =>
        (hT l (Finset.mem_insert_of_mem hl)).trans (hT a (Finset.mem_insert_self a T)).symm
      have hend : ∀ l ∈ T, σ.C l ≤ σ.S a := by
        intro l hl
        have hne : l ≠ a := fun h => haT (h ▸ hl)
        rcases σ.noOverlap l a hne (hmu l hl) with h | h
        · exact h
        · have := hmax l hl
          linarith
      have hsum := ih (fun l hl => hT l (Finset.mem_insert_of_mem hl)) (σ.S a)
        (σ.S_nonneg a) hend
      rw [Finset.sum_insert haT]
      have hCa := hC a (Finset.mem_insert_self a T)
      unfold Schedule.C at hCa
      linarith
  refine key _ (fun j hj => (Finset.mem_filter.mp hj).2) _ (LPLB.makespan_nonneg σ) ?_
  intro j _
  exact LPLB.le_makespan σ j

open UniformPrecSched.Makespan in
/-- Every feasible schedule yields a feasible LP solution with `D = C_max`. -/
theorem LPLB.sched_feasible {n m : ℕ} {I : Instance n m} (σ : Schedule I) :
    ∃ x C, LPFeasible I x C σ.makespan := by
  classical
  choose k hk using fun j => LPLB.exists_class I (σ.μ j)
  have hp : ∀ j, ∑ κ, I.p j / classSpeed I κ * xhat I k κ j = I.p j / I.s (σ.μ j) := by
    intro j
    simp [xhat, hk]
  refine ⟨xhat I k, σ.C, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j; simp [xhat]
  · intro κ
    have hs := LPLB.classSpeed_pos I κ
    have hc : (0 : ℝ) < classCount I κ := Nat.cast_pos.mpr (LPLB.classCount_pos I κ)
    have hsum : ∑ j, I.p j * xhat I k κ j
        = ∑ j ∈ Finset.univ.filter (fun j => k j = κ), I.p j := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun j _ => ?_
      unfold xhat
      by_cases h : k j = κ
      · subst h; simp
      · simp [h, Ne.symm h]
    have hmaps : ∀ j ∈ Finset.univ.filter (fun j => k j = κ),
        σ.μ j ∈ Finset.univ.filter (fun i => I.s i = classSpeed I κ) := by
      intro j hj
      have hkj := (Finset.mem_filter.mp hj).2
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [← hk j, hkj]
    have hload : ∑ j ∈ Finset.univ.filter (fun j => k j = κ), I.p j / classSpeed I κ
        ≤ (classCount I κ : ℝ) * σ.makespan := by
      calc ∑ j ∈ Finset.univ.filter (fun j => k j = κ), I.p j / classSpeed I κ
          = ∑ j ∈ Finset.univ.filter (fun j => k j = κ), I.p j / I.s (σ.μ j) := by
            refine Finset.sum_congr rfl fun j hj => ?_
            rw [← hk j, (Finset.mem_filter.mp hj).2]
        _ = ∑ i ∈ Finset.univ.filter (fun i => I.s i = classSpeed I κ),
              ∑ j ∈ (Finset.univ.filter (fun j => k j = κ)).filter (fun j => σ.μ j = i),
                I.p j / I.s (σ.μ j) :=
            (Finset.sum_fiberwise_of_maps_to hmaps _).symm
        _ ≤ ∑ i ∈ Finset.univ.filter (fun i => I.s i = classSpeed I κ), σ.makespan := by
            refine Finset.sum_le_sum fun i _ => ?_
            refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_) (LPLB.machine_load σ i)
            · intro j hj
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
              exact hj.2
            · intro j _ _
              exact (div_pos (I.p_pos j) (I.s_pos _)).le
        _ = (classCount I κ : ℝ) * σ.makespan := by
            simp [classCount]
    rw [hsum]
    rw [← Finset.sum_div, div_le_iff₀ hs] at hload
    rw [one_div, inv_mul_le_iff₀ (mul_pos hc hs)]
    linarith
  · intro j
    rw [hp j]
    unfold Schedule.C
    linarith [σ.S_nonneg j]
  · intro j' j h
    rw [hp j]
    have := σ.precedence j' j h
    unfold Schedule.C
    linarith
  · intro j
    exact LPLB.le_makespan σ j
  · intro κ j
    unfold xhat
    split_ifs <;> norm_num

open UniformPrecSched.Makespan in
theorem solution {n m : ℕ} (I : Instance n m) (x : Fin (numSpeeds I) → Fin n → ℝ)
    (C : Fin n → ℝ) (D : ℝ) (hLP : LPOptimal I x C D) (k : Assignment I)
    (hk : IsLPAssignment I x (Real.sqrt (numSpeeds I) + 1) k) (σ : Schedule I)
    (hσ : IsSpeedListSchedule I k σ) (σstar : Schedule I) :
    σ.makespan ≤
      ((numSpeeds I : ℝ) + 2 * Real.sqrt (numSpeeds I) + 1) * σstar.makespan := by
  have h1 := T35Aux.cor36 I x C D hLP k hk σ hσ
  obtain ⟨x', C', hf⟩ := LPLB.sched_feasible σstar
  have hD : D ≤ σstar.makespan := hLP.2 x' C' _ hf
  have hc : (0 : ℝ) ≤ (numSpeeds I : ℝ) + 2 * Real.sqrt (numSpeeds I) + 1 := by
    have := Real.sqrt_nonneg (numSpeeds I : ℝ)
    positivity
  exact h1.trans (mul_le_mul_of_nonneg_left hD hc)
