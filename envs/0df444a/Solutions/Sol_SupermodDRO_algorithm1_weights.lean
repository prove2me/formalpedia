-- Prove2me | solution 1 for SupermodDRO.algorithm1_weights
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T06:11:28.788547+00:00
-- url     : https://prove2.me/submissions/e1579d16-e4b6-4bc1-9d30-ac5ea3a184fc

import Mathlib
import Definitions.Def_SupermodDRO_ScenarioAssumptions
import Definitions.Def_SupermodDRO_algorithm1

set_option autoImplicit false

open SupermodDRO

namespace SupermodDRO.Alg1Proof

noncomputable def remMass (μ δ zl zu : ℝ) : Fin 3 → ℝ :=
  ![levelMass μ δ zl zu 1 + levelMass μ δ zl zu 2, levelMass μ δ zl zu 2, 0]

theorem levelMass_eq_of_lt {μ δ zl zu : ℝ} (h : zl < zu) :
    levelMass μ δ zl zu 0 = deltaHat μ δ zl zu / (2 * (μ - zl)) ∧
    levelMass μ δ zl zu 1 = 1 - deltaHat μ δ zl zu * (zu - zl) / (2 * (zu - μ) * (μ - zl)) ∧
    levelMass μ δ zl zu 2 = deltaHat μ δ zl zu / (2 * (zu - μ)) := by
  simp only [levelMass, if_pos h]
  exact ⟨rfl, rfl, rfl⟩

theorem levelMass_eq_of_not_lt {μ δ zl zu : ℝ} (h : ¬ zl < zu) :
    levelMass μ δ zl zu 0 = 1 ∧ levelMass μ δ zl zu 1 = 0 ∧ levelMass μ δ zl zu 2 = 0 := by
  simp only [levelMass, if_neg h]
  exact ⟨rfl, rfl, rfl⟩

theorem fin3_cases (c : Fin 3) : c = 0 ∨ c = 1 ∨ c = 2 := by
  fin_cases c <;> simp

theorem levelUp_zero : levelUp 0 = 1 := rfl
theorem levelUp_one : levelUp 1 = 2 := rfl
theorem levelUp_two : levelUp 2 = 2 := rfl

theorem remMass_zero (μ δ zl zu : ℝ) :
    remMass μ δ zl zu 0 = levelMass μ δ zl zu 1 + levelMass μ δ zl zu 2 := rfl
theorem remMass_one (μ δ zl zu : ℝ) : remMass μ δ zl zu 1 = levelMass μ δ zl zu 2 := rfl
theorem remMass_two (μ δ zl zu : ℝ) : remMass μ δ zl zu 2 = 0 := rfl

theorem levelMass_props {n : ℕ} {μ δ zl zu : Fin n → ℝ} (hsc : ScenarioAssumptions μ δ zl zu)
    (a : Fin n) :
    (∀ c : Fin 3, 0 ≤ levelMass (μ a) (δ a) (zl a) (zu a) c) ∧
    levelMass (μ a) (δ a) (zl a) (zu a) 0 + levelMass (μ a) (δ a) (zl a) (zu a) 1 +
      levelMass (μ a) (δ a) (zl a) (zu a) 2 = 1 ∧
    (zl a < zu a → 0 < levelMass (μ a) (δ a) (zl a) (zu a) 2) ∧
    (¬ zl a < zu a →
      levelMass (μ a) (δ a) (zl a) (zu a) 1 = 0 ∧
      levelMass (μ a) (δ a) (zl a) (zu a) 2 = 0) := by
  have hle1 : zl a ≤ μ a := hsc.ordered.1 a
  have hle2 : μ a ≤ zu a := hsc.ordered.2 a
  have hδnn : 0 ≤ δ a := hsc.delta_nonneg a
  by_cases hlt : zl a < zu a
  · have hμ_lt_zu : μ a < zu a := by
      by_contra h
      have heq : μ a = zu a := le_antisymm hle2 (not_lt.mp h)
      have ⟨⟨h1, h2⟩, _⟩ := hsc.wlog_mean a (Or.inl heq)
      linarith
    have hzl_lt_μ : zl a < μ a := by
      by_contra h
      have heq : μ a = zl a := le_antisymm (not_lt.mp h) hle1
      have ⟨⟨h1, h2⟩, _⟩ := hsc.wlog_mean a (Or.inr heq)
      linarith
    have hδ_pos : 0 < δ a := by
      by_contra h
      have heq : δ a = 0 := le_antisymm (not_lt.mp h) hδnn
      have ⟨h1, h2⟩ := hsc.wlog_delta a heq
      linarith
    have hd1 : 0 < μ a - zl a := sub_pos.mpr hzl_lt_μ
    have hd2 : 0 < zu a - μ a := sub_pos.mpr hμ_lt_zu
    have hd3 : 0 < zu a - zl a := sub_pos.mpr hlt
    have hprod : 0 < 2 * (zu a - μ a) * (μ a - zl a) := by
      have := mul_pos hd2 hd1
      linarith
    have hdh_pos : 0 < deltaHat (μ a) (δ a) (zl a) (zu a) :=
      lt_min hδ_pos (div_pos hprod hd3)
    have hdh_le : deltaHat (μ a) (δ a) (zl a) (zu a) ≤
        2 * (zu a - μ a) * (μ a - zl a) / (zu a - zl a) := min_le_right _ _
    have hm1_nn : 0 ≤ 1 - deltaHat (μ a) (δ a) (zl a) (zu a) * (zu a - zl a) /
        (2 * (zu a - μ a) * (μ a - zl a)) := by
      have hmul : deltaHat (μ a) (δ a) (zl a) (zu a) * (zu a - zl a) ≤
          2 * (zu a - μ a) * (μ a - zl a) := (le_div_iff₀ hd3).mp hdh_le
      have hdiv : deltaHat (μ a) (δ a) (zl a) (zu a) * (zu a - zl a) /
          (2 * (zu a - μ a) * (μ a - zl a)) ≤ 1 :=
        (div_le_one hprod).mpr hmul
      linarith
    obtain ⟨h0, h1, h2⟩ := levelMass_eq_of_lt (δ := δ a) hlt
    have hm0_nn : 0 ≤ deltaHat (μ a) (δ a) (zl a) (zu a) / (2 * (μ a - zl a)) :=
      div_nonneg hdh_pos.le (by linarith)
    have hm2_pos : 0 < deltaHat (μ a) (δ a) (zl a) (zu a) / (2 * (zu a - μ a)) :=
      div_pos hdh_pos (by linarith)
    refine ⟨?_, ?_, fun _ => by rw [h2]; exact hm2_pos, fun h => absurd hlt h⟩
    · intro c
      rcases fin3_cases c with rfl | rfl | rfl
      · rw [h0]; exact hm0_nn
      · rw [h1]; exact hm1_nn
      · rw [h2]; exact hm2_pos.le
    · rw [h0, h1, h2]
      have hne1 : (μ a - zl a) ≠ 0 := hd1.ne'
      have hne2 : (zu a - μ a) ≠ 0 := hd2.ne'
      have key : deltaHat (μ a) (δ a) (zl a) (zu a) * (zu a - zl a) /
          (2 * (zu a - μ a) * (μ a - zl a)) =
          deltaHat (μ a) (δ a) (zl a) (zu a) / (2 * (μ a - zl a)) +
          deltaHat (μ a) (δ a) (zl a) (zu a) / (2 * (zu a - μ a)) := by
        field_simp
        ring
      linarith
  · obtain ⟨h0, h1, h2⟩ := levelMass_eq_of_not_lt (μ := μ a) (δ := δ a) hlt
    refine ⟨?_, ?_, fun h => absurd h hlt, fun _ => ⟨h1, h2⟩⟩
    · intro c
      rcases fin3_cases c with rfl | rfl | rfl
      · simp [h0]
      · simp [h1]
      · simp [h2]
    · rw [h0, h1, h2]; norm_num

theorem exists_eq_ciInf {n : ℕ} (hn : 0 < n) (q : Fin n → ℝ) :
    (∃ a : Fin n, q a = ⨅ b, q b) ∧ ∀ b : Fin n, (⨅ c, q c) ≤ q b := by
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  obtain ⟨a₀, _, ha₀⟩ := Finset.exists_min_image Finset.univ q hne
  have hbdd : BddBelow (Set.range q) := ⟨q a₀, by rintro _ ⟨b, rfl⟩; exact ha₀ b (Finset.mem_univ b)⟩
  have hle_all : ∀ b : Fin n, (⨅ c, q c) ≤ q b := fun b => ciInf_le hbdd b
  have hge : q a₀ ≤ ⨅ c, q c := by
    haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    exact le_ciInf fun c => ha₀ c (Finset.mem_univ c)
  exact ⟨⟨a₀, le_antisymm hge (hle_all a₀)⟩, hle_all⟩

theorem remMass_nonneg {n : ℕ} {μ δ zl zu : Fin n → ℝ} (hsc : ScenarioAssumptions μ δ zl zu)
    (a : Fin n) (c : Fin 3) : 0 ≤ remMass (μ a) (δ a) (zl a) (zu a) c := by
  have hm := (levelMass_props hsc a).1
  rcases fin3_cases c with rfl | rfl | rfl
  · rw [remMass_zero]; exact add_nonneg (hm 1) (hm 2)
  · rw [remMass_one]; exact hm 2
  · rw [remMass_two]

end SupermodDRO.Alg1Proof

open SupermodDRO.Alg1Proof in
theorem solution {n : ℕ} (μ δ zl zu : Fin n → ℝ) (hsc : ScenarioAssumptions μ δ zl zu)
    (hn : 0 < n) :
    (∀ i, 0 ≤ algorithm1Weight μ δ zl zu i ∧ algorithm1Weight μ δ zl zu i ≤ 1) ∧
      ∑ i, algorithm1Weight μ δ zl zu i = 1 := by
  let S : ℕ → (Fin n → Fin 3) × (Fin n → ℝ) := algorithm1State μ δ zl zu
  let pNat : ℕ → ℝ := fun k => ⨅ a : Fin n, (S k).2 a
  let W : ℕ → ℝ := fun k => ∑ t ∈ Finset.range k, pNat t
  have hinv : ∀ k : ℕ, k ≤ 2 * n →
      (∀ a : Fin n, 0 ≤ (S k).2 a) ∧
      (((∀ a : Fin n, (S k).2 a + remMass (μ a) (δ a) (zl a) (zu a) ((S k).1 a) = 1 - W k) ∧
          ∑ a : Fin n, ((S k).1 a : ℕ) = k) ∨
        (W k = 1 ∧ ∃ a₀ : Fin n, ¬ zl a₀ < zu a₀ ∧ (S k).2 a₀ = 0)) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨?_, Or.inl ⟨?_, ?_⟩⟩
      · intro a
        exact (levelMass_props hsc a).1 0
      · intro a
        have hsum := (levelMass_props hsc a).2.1
        have hW0 : W 0 = 0 := Finset.sum_range_zero pNat
        have hS0 : S 0 = (fun _ => 0, fun i => levelMass (μ i) (δ i) (zl i) (zu i) 0) := rfl
        rw [hW0, hS0]
        dsimp only
        rw [remMass_zero]
        linarith
      · simp [S, algorithm1State]
    | succ k ih =>
      intro hk_succ
      have hk_lt : k < 2 * n := Nat.lt_of_succ_le hk_succ
      obtain ⟨hq_nn, hphase⟩ := ih (Nat.le_of_lt hk_lt)
      obtain ⟨hex_min, hmin_le⟩ := exists_eq_ciInf hn (S k).2
      have hex : ∃ a, (S k).2 a = pNat k := hex_min
      have hmin : ∀ a, pNat k ≤ (S k).2 a := fun a => hmin_le a
      let r : Fin n := Fin.find (fun a => (S k).2 a = pNat k) hex
      have hr_eq : (S k).2 r = pNat k := Fin.find_spec (p := fun a => (S k).2 a = pNat k) hex
      have hS_succ : S (k + 1) =
          (Function.update (S k).1 r (levelUp ((S k).1 r)),
            Function.update (fun a => (S k).2 a - pNat k) r
              (levelMass (μ r) (δ r) (zl r) (zu r) (levelUp ((S k).1 r)))) := by
        simp only [S, algorithm1State, algorithm1Step]
        change (if h : ∃ i, (S k).2 i = pNat k then
            (Function.update (S k).1 (Fin.find (fun i => (S k).2 i = pNat k) h)
                (levelUp ((S k).1 (Fin.find (fun i => (S k).2 i = pNat k) h))),
              Function.update (fun i => (S k).2 i - pNat k)
                (Fin.find (fun i => (S k).2 i = pNat k) h)
                (levelMass (μ (Fin.find (fun i => (S k).2 i = pNat k) h))
                  (δ (Fin.find (fun i => (S k).2 i = pNat k) h))
                  (zl (Fin.find (fun i => (S k).2 i = pNat k) h))
                  (zu (Fin.find (fun i => (S k).2 i = pNat k) h))
                  (levelUp ((S k).1 (Fin.find (fun i => (S k).2 i = pNat k) h)))))
          else ((S k).1, fun i => (S k).2 i - pNat k)) = _
        rw [dif_pos hex]
      have hq_r : (S (k + 1)).2 r = levelMass (μ r) (δ r) (zl r) (zu r) (levelUp ((S k).1 r)) := by
        rw [hS_succ]; dsimp only; rw [Function.update_self]
      have hq_ne : ∀ a, a ≠ r → (S (k + 1)).2 a = (S k).2 a - pNat k := by
        intro a h; rw [hS_succ]; dsimp only; rw [Function.update_of_ne h]
      have hL_r : (S (k + 1)).1 r = levelUp ((S k).1 r) := by
        rw [hS_succ]; dsimp only; rw [Function.update_self]
      have hL_ne : ∀ a, a ≠ r → (S (k + 1)).1 a = (S k).1 a := by
        intro a h; rw [hS_succ]; dsimp only; rw [Function.update_of_ne h]
      have hW_succ : W (k + 1) = W k + pNat k := Finset.sum_range_succ pNat k
      have hq_succ_nn : ∀ a : Fin n, 0 ≤ (S (k + 1)).2 a := by
        intro a
        by_cases har : a = r
        · rw [har, hq_r]
          exact (levelMass_props hsc r).1 _
        · rw [hq_ne a har]
          have := hmin a
          linarith
      refine ⟨hq_succ_nn, ?_⟩
      rcases hphase with ⟨hbal, hsumL⟩ | ⟨hW1, a₀, ha₀_deg, ha₀_zero⟩
      · by_cases hLr : ((S k).1 r : ℕ) < 2
        · left
          refine ⟨?_, ?_⟩
          · intro a
            rw [hW_succ]
            by_cases har : a = r
            · rw [har, hq_r, hL_r]
              have hbal_r := hbal r
              rw [hr_eq] at hbal_r
              rcases fin3_cases ((S k).1 r) with hc | hc | hc
              · rw [hc] at hbal_r ⊢
                rw [levelUp_zero, remMass_one]
                rw [remMass_zero] at hbal_r
                linarith
              · rw [hc] at hbal_r ⊢
                rw [levelUp_one, remMass_two]
                rw [remMass_one] at hbal_r
                linarith
              · rw [hc] at hLr
                exact absurd hLr (by decide)
            · rw [hq_ne a har, hL_ne a har]
              have hbal_a := hbal a
              linarith
          · have hstep_val : (levelUp ((S k).1 r) : ℕ) = ((S k).1 r : ℕ) + 1 := by
              rcases fin3_cases ((S k).1 r) with hc | hc | hc
              · rw [hc]; rfl
              · rw [hc]; rfl
              · rw [hc] at hLr
                exact absurd hLr (by decide)
            have hupd_sum : ∑ a : Fin n, ((S (k + 1)).1 a : ℕ) =
                (∑ a : Fin n, ((S k).1 a : ℕ)) + 1 := by
              rw [← Finset.add_sum_erase _ _ (Finset.mem_univ r),
                ← Finset.add_sum_erase _ (fun a : Fin n => ((S k).1 a : ℕ)) (Finset.mem_univ r)]
              have heq_rest : ∑ x ∈ Finset.univ.erase r, ((S (k + 1)).1 x : ℕ) =
                  ∑ x ∈ Finset.univ.erase r, ((S k).1 x : ℕ) := by
                refine Finset.sum_congr rfl fun x hx => ?_
                rw [hL_ne x (Finset.ne_of_mem_erase hx)]
              rw [heq_rest, hL_r, hstep_val]
              omega
            rw [hupd_sum, hsumL]
        · right
          have hLr2 : (S k).1 r = 2 := by
            ext
            have hlt3 := ((S k).1 r).isLt
            change ((S k).1 r : ℕ) = 2
            omega
          have hbal_r := hbal r
          rw [hr_eq, hLr2, remMass_two] at hbal_r
          have hW_next : W (k + 1) = 1 := by rw [hW_succ]; linarith
          have hex_lt2 : ∃ a₀ : Fin n, ((S k).1 a₀ : ℕ) < 2 := by
            by_contra hall
            push Not at hall
            have hge2n : 2 * n ≤ ∑ a : Fin n, ((S k).1 a : ℕ) := by
              have hcard : ∑ _a : Fin n, (2 : ℕ) = 2 * n := by
                simp [Nat.mul_comm]
              rw [← hcard]
              exact Finset.sum_le_sum fun a _ => hall a
            omega
          obtain ⟨a₀, ha₀_lt2⟩ := hex_lt2
          have ha₀_ne_r : a₀ ≠ r := by
            intro heq
            rw [heq, hLr2] at ha₀_lt2
            exact absurd ha₀_lt2 (by decide)
          have hbal_a₀ := hbal a₀
          have hmin_a₀ := hmin a₀
          have hrem_nn := remMass_nonneg hsc a₀ ((S k).1 a₀)
          have hrem_zero : remMass (μ a₀) (δ a₀) (zl a₀) (zu a₀) ((S k).1 a₀) = 0 := by
            linarith
          have hqa₀_eq_p : (S k).2 a₀ = pNat k := by linarith
          have ha₀_deg : ¬ zl a₀ < zu a₀ := by
            intro hlt_a₀
            have hm2_pos := (levelMass_props hsc a₀).2.2.1 hlt_a₀
            have hm1_nn := (levelMass_props hsc a₀).1 1
            rcases fin3_cases ((S k).1 a₀) with hc | hc | hc
            · rw [hc, remMass_zero] at hrem_zero
              linarith
            · rw [hc, remMass_one] at hrem_zero
              linarith
            · rw [hc] at ha₀_lt2
              exact absurd ha₀_lt2 (by decide)
          refine ⟨hW_next, a₀, ha₀_deg, ?_⟩
          rw [hq_ne a₀ ha₀_ne_r, hqa₀_eq_p, sub_self]
      · right
        have hp0 : pNat k = 0 := by
          have hle0 := hmin a₀
          rw [ha₀_zero] at hle0
          have hge0 := hq_nn r
          rw [hr_eq] at hge0
          linarith
        refine ⟨by rw [hW_succ, hW1, hp0, add_zero], a₀, ha₀_deg, ?_⟩
        by_cases har : a₀ = r
        · rw [har] at ha₀_deg ⊢
          rw [hq_r]
          obtain ⟨hm1, hm2⟩ := (levelMass_props hsc r).2.2.2 ha₀_deg
          rcases fin3_cases ((S k).1 r) with hc | hc | hc
          · rw [hc, levelUp_zero]; exact hm1
          · rw [hc, levelUp_one]; exact hm2
          · rw [hc, levelUp_two]; exact hm2
        · rw [hq_ne a₀ har, ha₀_zero, hp0, sub_zero]
  have hw_eq : ∀ j : Fin (2 * n + 1), algorithm1Weight μ δ zl zu j = pNat j.val := fun _ => rfl
  have hp_nonneg : ∀ j : Fin (2 * n + 1), 0 ≤ algorithm1Weight μ δ zl zu j := by
    intro j
    obtain ⟨hq_nn, _⟩ := hinv j.val (Nat.lt_succ_iff.mp j.isLt)
    obtain ⟨⟨a₀, ha₀⟩, _⟩ := exists_eq_ciInf hn (S j.val).2
    rw [hw_eq]
    change 0 ≤ ⨅ i, (S j.val).2 i
    rw [← ha₀]
    exact hq_nn a₀
  have hsum_one : ∑ j : Fin (2 * n + 1), algorithm1Weight μ δ zl zu j = 1 := by
    have hfin_range : (∑ j : Fin (2 * n + 1), algorithm1Weight μ δ zl zu j) =
        W (2 * n) + pNat (2 * n) := by
      simp only [hw_eq]
      rw [Fin.sum_univ_eq_sum_range (fun t => pNat t) (2 * n + 1), Finset.sum_range_succ]
    rw [hfin_range]
    obtain ⟨hq_nn, hphase⟩ := hinv (2 * n) le_rfl
    obtain ⟨hex_min, hmin_le⟩ := exists_eq_ciInf hn (S (2 * n)).2
    obtain ⟨r, hr_eq⟩ := hex_min
    have hr_eq' : (S (2 * n)).2 r = pNat (2 * n) := hr_eq
    have hmin : ∀ a, pNat (2 * n) ≤ (S (2 * n)).2 a := fun a => hmin_le a
    rcases hphase with ⟨hbal, hsumL⟩ | ⟨hW1, a₀, _, ha₀_zero⟩
    · have hall2 : ∀ a : Fin n, ((S (2 * n)).1 a : ℕ) = 2 := by
        have hsum2 : ∑ a : Fin n, ((S (2 * n)).1 a : ℕ) = ∑ _a : Fin n, (2 : ℕ) := by
          rw [hsumL]
          simp [Nat.mul_comm]
        have hle2 : ∀ a ∈ (Finset.univ : Finset (Fin n)), ((S (2 * n)).1 a : ℕ) ≤ 2 := by
          intro a _
          have := ((S (2 * n)).1 a).isLt
          omega
        exact fun a => (Finset.sum_eq_sum_iff_of_le hle2).mp hsum2 a (Finset.mem_univ a)
      have hLr2 : (S (2 * n)).1 r = 2 := by
        ext
        exact hall2 r
      have hbal_r := hbal r
      rw [hr_eq', hLr2, remMass_two] at hbal_r
      linarith
    · have hp0 : pNat (2 * n) = 0 := by
        have hle0 := hmin a₀
        rw [ha₀_zero] at hle0
        have hge0 := hq_nn r
        rw [hr_eq'] at hge0
        linarith
      linarith
  refine ⟨fun j => ⟨hp_nonneg j, ?_⟩, hsum_one⟩
  rw [← hsum_one]
  exact Finset.single_le_sum (f := algorithm1Weight μ δ zl zu)
    (fun k _ => hp_nonneg k) (Finset.mem_univ j)
