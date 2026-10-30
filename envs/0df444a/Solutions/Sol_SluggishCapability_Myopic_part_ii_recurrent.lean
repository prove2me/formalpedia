-- Prove2me | solution 1 for SluggishCapability.Myopic.part_ii_recurrent
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T00:52:41.944482+00:00
-- url     : https://prove2.me/submissions/9d8db689-424e-4958-884b-27170e15d8cf

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_SluggishCapability_Myopic_Setting
import Theorems.Thm_SluggishCapability_Myopic_ext_marginal_stationary

open MarkovMixing
open SluggishCapability.Myopic

namespace SlugPart2Aux

variable {X : Type*} [Fintype X] [DecidableEq X]

lemma pow_nonneg' (K : Matrix X X ℝ) (hK : ∀ x y, 0 ≤ K x y) :
    ∀ t : ℕ, ∀ x y, 0 ≤ (K ^ t) x y := by
  intro t
  induction t with
  | zero => intro x y; simp only [pow_zero, Matrix.one_apply]; split_ifs <;> norm_num
  | succ t ih =>
    intro x y
    rw [pow_succ, Matrix.mul_apply]
    exact Finset.sum_nonneg fun w _ => mul_nonneg (ih x w) (hK w y)

lemma pow_rowsum (K : Matrix X X ℝ) (hK : ∀ x, ∑ y, K x y = 1) :
    ∀ t : ℕ, ∀ x, ∑ y, (K ^ t) x y = 1 := by
  intro t
  induction t with
  | zero => intro x; simp [Matrix.one_apply]
  | succ t ih =>
    intro x
    simp_rw [pow_succ, Matrix.mul_apply]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hK, mul_one]
    exact ih x

lemma reaches_refl (K : Matrix X X ℝ) (x : X) : Reaches K x x :=
  ⟨0, by simp⟩

lemma reaches_of_pos (K : Matrix X X ℝ) {x y : X} (h : 0 < K x y) : Reaches K x y :=
  ⟨1, by simpa using h⟩

lemma reaches_trans (K : Matrix X X ℝ) (hK : ∀ x y, 0 ≤ K x y) {x y z : X}
    (h1 : Reaches K x y) (h2 : Reaches K y z) : Reaches K x z := by
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b, hb⟩ := h2
  refine ⟨a + b, ?_⟩
  rw [pow_add, Matrix.mul_apply]
  have hle : (K ^ a) x y * (K ^ b) y z ≤ ∑ w, (K ^ a) x w * (K ^ b) w z :=
    Finset.single_le_sum (f := fun w => (K ^ a) x w * (K ^ b) w z)
      (fun w _ => mul_nonneg (pow_nonneg' K hK a x w) (pow_nonneg' K hK b w z))
      (Finset.mem_univ y)
  exact lt_of_lt_of_le (mul_pos ha hb) hle

lemma closed_pow (K : Matrix X X ℝ) (hK : ∀ x y, 0 ≤ K x y) (C : X → Prop)
    (hC : ∀ y z, C y → 0 < K y z → C z) :
    ∀ t : ℕ, ∀ y z, C y → 0 < (K ^ t) y z → C z := by
  intro t
  induction t with
  | zero =>
    intro y z hy h
    simp only [pow_zero, Matrix.one_apply] at h
    split_ifs at h with hyz
    · exact hyz ▸ hy
    · norm_num at h
  | succ t ih =>
    intro y z hy h
    by_contra hz
    rw [pow_succ, Matrix.mul_apply] at h
    have : ∑ w, (K ^ t) y w * K w z ≤ 0 := by
      apply Finset.sum_nonpos
      intro w _
      rcases (pow_nonneg' K hK t y w).lt_or_eq with h1 | h1
      · rcases (hK w z).lt_or_eq with h2 | h2
        · exact absurd (hC w z (ih y w hy h1) h2) hz
        · rw [← h2]; simp
      · rw [← h1]; simp
    linarith

lemma stat_pow (K : Matrix X X ℝ) (ν : X → ℝ) (hν : Matrix.vecMul ν K = ν) :
    ∀ t : ℕ, Matrix.vecMul ν (K ^ t) = ν := by
  intro t
  induction t with
  | zero => simp
  | succ t ih => rw [pow_succ, ← Matrix.vecMul_vecMul, ih, hν]

/-- A stationary law vanishes at a state outside a closed set `C` from which `C` is reachable. -/
lemma stat_zero_off_closed (K : Matrix X X ℝ) (hK : IsStochastic K) (C : X → Prop)
    [DecidablePred C] (hC : ∀ y z, C y → 0 < K y z → C z)
    (ν : X → ℝ) (hν : IsStationary K ν) (y c : X) (hy : ¬ C y) (hc : C c) (t : ℕ)
    (ht : 0 < (K ^ t) y c) : ν y = 0 := by
  have hK0 := hK.1
  have hst := stat_pow K ν hν.2 t
  let R : X → ℝ := fun w => ∑ z, if C z then (K ^ t) w z else 0
  have hR0 : ∀ w, 0 ≤ R w := fun w =>
    Finset.sum_nonneg fun z _ => by split_ifs; exacts [pow_nonneg' K hK0 t w z, le_rfl]
  have hR1 : ∀ w, C w → R w = 1 := by
    intro w hw
    rw [← pow_rowsum K hK.2 t w]
    refine Finset.sum_congr rfl fun z _ => ?_
    split_ifs with hz
    · rfl
    · exact (le_antisymm (not_lt.mp fun h => hz (closed_pow K hK0 C hC t w z hw h))
        (pow_nonneg' K hK0 t w z)).symm
  have hRy : 0 < R y := by
    have : (if C c then (K ^ t) y c else 0) ≤ R y :=
      Finset.single_le_sum (f := fun z => if C z then (K ^ t) y z else 0)
        (fun z _ => by split_ifs; exacts [pow_nonneg' K hK0 t y z, le_rfl]) (Finset.mem_univ c)
    rw [if_pos hc] at this; linarith
  -- mass of `C`
  have hmass : ∑ z, (if C z then ν z else 0) = ∑ w, ν w * R w := by
    calc ∑ z, (if C z then ν z else 0)
        = ∑ z, (if C z then ∑ w, ν w * (K ^ t) w z else 0) := by
          refine Finset.sum_congr rfl fun z _ => ?_
          have := congrFun hst z
          simp only [Matrix.vecMul, dotProduct] at this
          rw [this]
      _ = ∑ z, ∑ w, ν w * (if C z then (K ^ t) w z else 0) := by
          refine Finset.sum_congr rfl fun z _ => ?_
          split_ifs <;> simp
      _ = ∑ w, ν w * R w := by rw [Finset.sum_comm]; simp_rw [R, Finset.mul_sum]
  have hsplit : ∑ w, ν w * R w =
      ∑ w, (if C w then ν w else 0) + ∑ w, (if C w then 0 else ν w * R w) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    split_ifs with hw
    · rw [hR1 w hw]; ring
    · ring
  have hzero : ∑ w, (if C w then 0 else ν w * R w) = 0 := by linarith
  have hnn : ∀ w ∈ Finset.univ, 0 ≤ (if C w then 0 else ν w * R w) := fun w _ => by
    split_ifs; exacts [le_rfl, mul_nonneg (hν.1.1 w) (hR0 w)]
  have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hzero y (Finset.mem_univ y)
  rw [if_neg hy] at this
  rcases mul_eq_zero.mp this with h | h
  · exact h
  · linarith

lemma sum_two (a b : X) (hab : a ≠ b) (ν G : X → ℝ)
    (h : ∀ w, w ≠ a → w ≠ b → ν w = 0) : ∑ w, ν w * G w = ν a * G a + ν b * G b := by
  rw [← Finset.sum_subset (s₁ := {a, b}) (Finset.subset_univ _)
    (fun w _ hw => by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hw
      rw [h w hw.1 hw.2, zero_mul])]
  exact Finset.sum_pair hab

end SlugPart2Aux

open SlugPart2Aux

theorem solution (μ : ℕ) (hμ : 1 ≤ μ) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (M : ℕ) (hM : 2 * μ ≤ M) :
    (∀ x : Fin (M + 1) × Fin 2, IsRecurrentState (extKernel (twoStateP β) (twoStateF μ) M) x ↔
      (((x.1 : ℕ) = 2 * μ - 1 ∧ x.2 = 0) ∨ ((x.1 : ℕ) = 2 * μ ∧ x.2 = 1))) ∧
    (∃ ν : Fin (M + 1) × Fin 2 → ℝ, IsStationary (extKernel (twoStateP β) (twoStateF μ) M) ν) ∧
    ∀ ν : Fin (M + 1) × Fin 2 → ℝ, IsStationary (extKernel (twoStateP β) (twoStateF μ) M) ν →
      ∀ x : Fin (M + 1) × Fin 2,
        ((x.1 : ℕ) = 2 * μ → x.2 = 1 → ν x = 1 / (1 + β)) ∧
        ((x.1 : ℕ) = 2 * μ - 1 → x.2 = 0 → ν x = β / (1 + β)) := by
  classical
  set K := extKernel (twoStateP β) (twoStateF μ) M with hKdef
  have hP00 : twoStateP β 0 0 = 0 := by simp [twoStateP]
  have hP01 : twoStateP β 0 1 = 1 := by simp [twoStateP]
  have hP10 : twoStateP β 1 0 = β := by simp [twoStateP]
  have hP11 : twoStateP β 1 1 = 1 - β := by simp [twoStateP]
  have hF0 : twoStateF μ 0 = 0 := by simp [twoStateF]
  have hF1 : twoStateF μ 1 = 2 * μ := by simp [twoStateF]
  have hPnn : ∀ s s' : Fin 2, 0 ≤ twoStateP β s s' := by
    intro s s'; fin_cases s <;> fin_cases s' <;> simp [hP00, hP01, hP10, hP11] <;> linarith
  have hPH : ∀ s : Fin 2, 0 < twoStateP β s 1 := by
    intro s; fin_cases s <;> simp [hP01, hP11] <;> linarith
  have hKval : ∀ (m : Fin (M + 1)) (s : Fin 2) (m' : Fin (M + 1)) (s' : Fin 2),
      K (m, s) (m', s') =
        if (m' : ℕ) = myopicStep m (twoStateF μ s') then twoStateP β s s' else 0 := by
    intro m s m' s'; rfl
  have hK0 : ∀ x y, 0 ≤ K x y := by
    rintro ⟨m, s⟩ ⟨m', s'⟩; rw [hKval]; split_ifs; exacts [hPnn s s', le_rfl]
  have hKst : IsStochastic K :=
    (ext_marginal_stationary (twoStateP β) (twoStateF μ) M
      ⟨fun s s' => hPnn s s', fun s => by fin_cases s <;> simp [Fin.sum_univ_two, hP00, hP01, hP10, hP11]⟩
      (fun s => by fin_cases s <;> simp [hF0, hF1] <;> omega)).1
  have ms1 : myopicStep (2 * μ - 1) (2 * μ) = 2 * μ := by unfold myopicStep; split_ifs <;> omega
  have ms2 : myopicStep (2 * μ) 0 = 2 * μ - 1 := by unfold myopicStep; split_ifs <;> omega
  have ms3 : myopicStep (2 * μ) (2 * μ) = 2 * μ := by unfold myopicStep; split_ifs <;> omega
  have hlt1 : 2 * μ - 1 < M + 1 := by omega
  have hlt2 : 2 * μ < M + 1 := by omega
  set a : Fin (M + 1) × Fin 2 := (⟨2 * μ - 1, hlt1⟩, 0) with ha_def
  set b : Fin (M + 1) × Fin 2 := (⟨2 * μ, hlt2⟩, 1) with hb_def
  have hab : a ≠ b := by
    intro h; have := congrArg Prod.snd h; simp [a, b] at this
  have hKab : K a b = 1 := by
    rw [ha_def, hb_def, hKval]; simp [hF1, ms1, hP01]
  have hKba : K b a = β := by
    rw [ha_def, hb_def, hKval]; simp [hF0, ms2, hP10]
  have hKaa : K a a = 0 := by
    rw [ha_def, hKval]; simp [hP00]
  have hKbb : K b b = 1 - β := by
    rw [hb_def, hKval]; simp [hF1, ms3, hP11]
  let C : Fin (M + 1) × Fin 2 → Prop := fun y => y = a ∨ y = b
  have hC : ∀ y z, C y → 0 < K y z → C z := by
    rintro y ⟨m', s'⟩ hy h
    rcases hy with rfl | rfl
    · rw [ha_def, hKval] at h
      obtain rfl | rfl : s' = 0 ∨ s' = 1 := by fin_cases s' <;> simp
      · simp [hP00] at h
      · split_ifs at h with hc
        · right
          simp only [hF1, ms1] at hc
          rw [hb_def]; exact Prod.ext (Fin.ext hc) rfl
        · simp at h
    · rw [hb_def, hKval] at h
      obtain rfl | rfl : s' = 0 ∨ s' = 1 := by fin_cases s' <;> simp
      · split_ifs at h with hc
        · left
          simp only [hF0, ms2] at hc
          rw [ha_def]; exact Prod.ext (Fin.ext hc) rfl
        · simp at h
      · split_ifs at h with hc
        · right
          simp only [hF1, ms3] at hc
          rw [hb_def]; exact Prod.ext (Fin.ext hc) rfl
        · simp at h
  -- every state reaches `b`
  have hg : ∀ m : ℕ, m < M + 1 → myopicStep m (2 * μ) < M + 1 := by
    intro m hm; unfold myopicStep; split_ifs <;> omega
  have hstepG : ∀ (m : Fin (M + 1)) (s : Fin 2),
      0 < K (m, s) (⟨myopicStep m (2 * μ), hg m m.2⟩, 1) := by
    intro m s
    rw [hKval, if_pos (by simp [hF1])]
    exact hPH s
  have hstepB : ∀ (m : Fin (M + 1)) (s : Fin 2), (m : ℕ) = 2 * μ → Reaches K (m, s) b := by
    intro m s hm
    have h := hstepG m s
    have : ((⟨myopicStep m (2 * μ), hg m m.2⟩ : Fin (M + 1)), (1 : Fin 2)) = b := by
      rw [hb_def]; refine Prod.ext (Fin.ext ?_) rfl
      simp only [hm, ms3]
    rw [this] at h
    exact reaches_of_pos K h
  have hR : ∀ n : ℕ, ∀ (m : Fin (M + 1)) (s : Fin 2),
      ((m : ℕ) - 2 * μ) + (2 * μ - m) ≤ n → Reaches K (m, s) b := by
    intro n
    induction n with
    | zero => intro m s hd; exact hstepB m s (by omega)
    | succ n ih =>
      intro m s hd
      by_cases hm : (m : ℕ) = 2 * μ
      · exact hstepB m s hm
      · refine reaches_trans K hK0 (reaches_of_pos K (hstepG m s)) (ih _ 1 ?_)
        simp only
        unfold myopicStep; split_ifs <;> omega
  have hRall : ∀ x, Reaches K x b := fun x => hR _ x.1 x.2 le_rfl
  have hreachC : ∀ y z, C y → C z → Reaches K y z := by
    have hab' := reaches_of_pos K (show 0 < K a b by rw [hKab]; norm_num)
    have hba' := reaches_of_pos K (show 0 < K b a by rw [hKba]; exact hβ0)
    rintro y z (rfl | rfl) (rfl | rfl)
    exacts [reaches_refl K _, hab', hba', reaches_refl K _]
  have hCiff : ∀ x : Fin (M + 1) × Fin 2, C x ↔
      (((x.1 : ℕ) = 2 * μ - 1 ∧ x.2 = 0) ∨ ((x.1 : ℕ) = 2 * μ ∧ x.2 = 1)) := by
    rintro ⟨m, s⟩
    constructor
    · rintro (h | h)
      · left; rw [ha_def] at h; simp only [Prod.mk.injEq] at h; rw [h.1, h.2]; exact ⟨rfl, rfl⟩
      · right; rw [hb_def] at h; simp only [Prod.mk.injEq] at h; rw [h.1, h.2]; exact ⟨rfl, rfl⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · left; rw [ha_def]; exact Prod.ext (Fin.ext h1) h2
      · right; rw [hb_def]; exact Prod.ext (Fin.ext h1) h2
  -- stationary laws vanish off `C`
  have hoff : ∀ ν, IsStationary K ν → ∀ w, w ≠ a → w ≠ b → ν w = 0 := by
    intro ν hν w hwa hwb
    obtain ⟨t, ht⟩ := hRall w
    exact stat_zero_off_closed K hKst C hC ν hν w b (by rintro (h | h) <;> contradiction)
      (Or.inr rfl) t ht
  refine ⟨fun x => ⟨fun hx => ?_, fun hx => ?_⟩, ?_, ?_⟩
  · obtain ⟨t, ht⟩ := hx b (hRall x)
    exact (hCiff x).mp (closed_pow K hK0 C hC t b x (Or.inr rfl) ht)
  · intro y hy
    obtain ⟨t, ht⟩ := hy
    have hCx := (hCiff x).mpr hx
    exact hreachC y x (closed_pow K hK0 C hC t x y hCx ht) hCx
  · let ν : Fin (M + 1) × Fin 2 → ℝ := fun z =>
      if z = a then β / (1 + β) else if z = b then 1 / (1 + β) else 0
    have hνa : ν a = β / (1 + β) := by simp [ν]
    have hνb : ν b = 1 / (1 + β) := by simp [ν, hab.symm]
    have hνoff : ∀ w, w ≠ a → w ≠ b → ν w = 0 := fun w h1 h2 => by simp [ν, h1, h2]
    have h1β : (0 : ℝ) < 1 + β := by linarith
    refine ⟨ν, ⟨fun z => ?_, ?_⟩, ?_⟩
    · simp only [ν]; split_ifs <;> positivity
    · have := sum_two a b hab ν (fun _ => 1) hνoff
      simp only [mul_one] at this
      rw [this, hνa, hνb]; field_simp; ring
    · funext z
      simp only [Matrix.vecMul, dotProduct]
      rw [sum_two a b hab ν (fun w => K w z) hνoff, hνa, hνb]
      by_cases hza : z = a
      · rw [hza, hKaa, hKba, hνa]; ring
      · by_cases hzb : z = b
        · rw [hzb, hKab, hKbb, hνb]; field_simp; ring
        · rw [hνoff z hza hzb]
          have h1 : K a z = 0 := by
            rcases (hK0 a z).lt_or_eq with h | h
            · rcases hC a z (Or.inl rfl) h with h' | h' <;> contradiction
            · exact h.symm
          have h2 : K b z = 0 := by
            rcases (hK0 b z).lt_or_eq with h | h
            · rcases hC b z (Or.inr rfl) h with h' | h' <;> contradiction
            · exact h.symm
          rw [h1, h2]; ring
  · intro ν hν x
    have hz := hoff ν hν
    have hsum := sum_two a b hab ν (fun _ => 1) hz
    simp only [mul_one] at hsum
    rw [hν.1.2] at hsum
    have hva : ν a = β * ν b := by
      have := congrFun hν.2 a
      simp only [Matrix.vecMul, dotProduct] at this
      rw [sum_two a b hab ν (fun w => K w a) hz, hKaa, hKba] at this
      linarith
    have h1β : (0 : ℝ) < 1 + β := by linarith
    have hvb : ν b = 1 / (1 + β) := by
      field_simp; linarith
    have hva' : ν a = β / (1 + β) := by rw [hva, hvb]; ring
    obtain ⟨m, s⟩ := x
    refine ⟨fun h1 h2 => ?_, fun h1 h2 => ?_⟩
    · have : ((m, s) : Fin (M + 1) × Fin 2) = b := by
        rw [hb_def]; exact Prod.ext (Fin.ext h1) h2
      rw [this, hvb]
    · have : ((m, s) : Fin (M + 1) × Fin 2) = a := by
        rw [ha_def]; exact Prod.ext (Fin.ext h1) h2
      rw [this, hva']
