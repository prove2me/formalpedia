-- Prove2me | solution 1 for TransparencyTeamContracts.Submodular.theorem_4_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-20T03:30:57.277481+00:00
-- url     : https://prove2.me/submissions/a3f62d6c-ac9b-40f4-94bb-8dff3580e22f

import Mathlib
import Definitions.Def_TransparencyTeamContracts_Submodular_Information

open Finset MeasureTheory
open scoped ENNReal Classical

namespace TransparencyTeamContracts_Submodular_Proof

open TransparencyTeamContracts.Submodular

/-! ### Section 1: Stateless Preliminaries & Equilibrium Characterizations -/

lemma effortTeam_teamProfile {n : ℕ} (S : Finset (Fin n)) :
    effortTeam (teamProfile S) = S := by
  ext i
  simp [effortTeam, teamProfile]

lemma effortTeam_update_false {n : ℕ} (S : Finset (Fin n)) (i : Fin n) :
    effortTeam (Function.update (teamProfile S) i false) = S.erase i := by
  ext j
  by_cases hj : j = i <;> simp [effortTeam, teamProfile, hj]

lemma effortTeam_update_true {n : ℕ} (S : Finset (Fin n)) (i : Fin n) :
    effortTeam (Function.update (teamProfile S) i true) = insert i S := by
  ext j
  by_cases hj : j = i <;> simp [effortTeam, teamProfile, hj]

lemma isEquilibrium_iff {n : ℕ} (f : Finset (Fin n) → ℝ) (c α : Fin n → ℝ)
    (S : Finset (Fin n)) :
    IsEquilibrium f c α S ↔
      (∀ i ∈ S, c i ≤ α i * (f S - f (S.erase i))) ∧
      (∀ i ∉ S, α i * (f (insert i S) - f S) ≤ c i) := by
  constructor
  · intro h
    rcases h with ⟨_, hbr⟩
    refine ⟨?_, ?_⟩
    · intro i hi
      have h0 := hbr i false (Set.mem_univ false)
      simp only [effortGame, effortTeam_update_false, effortTeam_teamProfile,
        agentUtility, mem_erase, ne_eq, not_true_eq_false, false_and, ↓reduceIte, hi] at h0
      linarith
    · intro i hi
      have h1 := hbr i true (Set.mem_univ true)
      simp only [effortGame, effortTeam_update_true, effortTeam_teamProfile,
        agentUtility, mem_insert, true_or, ↓reduceIte, hi] at h1
      linarith
  · rintro ⟨hin, hout⟩
    refine ⟨fun _ => Set.mem_univ _, fun i b _ => ?_⟩
    by_cases hi : i ∈ S
    · cases b
      · simp only [effortGame, effortTeam_update_false, effortTeam_teamProfile,
          agentUtility, mem_erase, ne_eq, not_true_eq_false, false_and, ↓reduceIte, hi]
        have := hin i hi
        linarith
      · have hup : Function.update (teamProfile S) i true = teamProfile S := by
          ext j
          by_cases hj : j = i <;> simp [teamProfile, hj, hi]
        rw [hup]
    · cases b
      · have hup : Function.update (teamProfile S) i false = teamProfile S := by
          ext j
          by_cases hj : j = i <;> simp [teamProfile, hj, hi]
        rw [hup]
      · simp only [effortGame, effortTeam_update_true, effortTeam_teamProfile,
          agentUtility, mem_insert, true_or, ↓reduceIte, hi]
        have := hout i hi
        linarith

lemma zero_contract_isContract {n : ℕ} : IsContract (fun _ : Fin n => (0 : ℝ)) := by
  intro i _
  exact ⟨le_refl 0, zero_le_one⟩

lemma zero_contract_equilibrium {n : ℕ} (f : Finset (Fin n) → ℝ) (c : Fin n → ℝ)
    (hc : ∀ i, 0 ≤ c i) :
    IsEquilibrium f c (fun _ => 0) (univ.filter (fun i => c i = 0)) := by
  rw [isEquilibrium_iff]
  refine ⟨fun i hi => ?_, fun i _ => ?_⟩
  · simp only [mem_filter, mem_univ, true_and] at hi
    simp [hi]
  · simp [hc i]

lemma statelessPayoffs_nonempty {n : ℕ} (f : Finset (Fin n) → ℝ) (c : Fin n → ℝ)
    (hc : ∀ i, 0 ≤ c i) :
    (statelessPayoffs f c).Nonempty := by
  refine ⟨principalUtility f (fun _ => 0) (univ.filter (fun i => c i = 0)),
    fun _ => 0, univ.filter (fun i => c i = 0), zero_contract_isContract,
    zero_contract_equilibrium f c hc, rfl⟩

lemma principalUtility_le_one {n : ℕ} {f : Finset (Fin n) → ℝ} (hf : IsSuccess f)
    {α : Fin n → ℝ} (hα : IsContract α) (S : Finset (Fin n)) :
    principalUtility f α S ≤ 1 := by
  unfold principalUtility
  have hsum_nonneg : 0 ≤ ∑ i, α i :=
    sum_nonneg (fun i _ => (hα i (mem_univ i)).1)
  have hf0 : 0 ≤ f S := (hf.2 S).1
  have hf1 : f S ≤ 1 := (hf.2 S).2
  nlinarith

lemma statelessPayoffs_bddAbove {n : ℕ} {f : Finset (Fin n) → ℝ} (hf : IsSuccess f)
    (c : Fin n → ℝ) :
    BddAbove (statelessPayoffs f c) := by
  refine ⟨1, ?_⟩
  rintro u ⟨α, S, hα, _, rfl⟩
  exact principalUtility_le_one hf hα S

lemma le_V_of_isEquilibrium {n : ℕ} {f : Finset (Fin n) → ℝ} (hf : IsSuccess f)
    {c α : Fin n → ℝ} {S : Finset (Fin n)}
    (hα : IsContract α) (heq : IsEquilibrium f c α S) :
    principalUtility f α S ≤ V f c :=
  le_csSup (statelessPayoffs_bddAbove hf c) ⟨α, S, hα, heq, rfl⟩

lemma V_nonneg {n : ℕ} {f : Finset (Fin n) → ℝ} (hf : IsSuccess f)
    {c : Fin n → ℝ} (hc : ∀ i, 0 ≤ c i) :
    0 ≤ V f c := by
  let S₀ := univ.filter (fun i : Fin n => c i = 0)
  have hle := le_V_of_isEquilibrium hf zero_contract_isContract (zero_contract_equilibrium f c hc)
  have hpu : 0 ≤ principalUtility f (fun _ => 0) S₀ := by
    simp [principalUtility, (hf.2 S₀).1]
  linarith

lemma le_V_of_team {n : ℕ} {f : Finset (Fin n) → ℝ} (hf : IsSuccess f)
    {c : Fin n → ℝ} (hc : ∀ i, 0 ≤ c i) (T : Finset (Fin n))
    (hm_pos : ∀ i ∈ T, 0 < f T - f (T.erase i))
    (hm_le : ∀ i ∈ T, c i / (f T - f (T.erase i)) ≤ 1) :
    (1 - ∑ i ∈ T, c i / (f T - f (T.erase i))) * f T ≤ V f c := by
  let α : Fin n → ℝ := fun i => if i ∈ T then c i / (f T - f (T.erase i)) else 0
  have hα : IsContract α := by
    intro i _
    by_cases hi : i ∈ T
    · simp only [α, hi, ↓reduceIte]
      exact ⟨div_nonneg (hc i) (le_of_lt (hm_pos i hi)), hm_le i hi⟩
    · simp [α, hi]
  have heq : IsEquilibrium f c α T := by
    rw [isEquilibrium_iff]
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · simp only [α, hi, ↓reduceIte]
      rw [div_mul_cancel₀ _ (ne_of_gt (hm_pos i hi))]
    · simp [α, hi, hc i]
  have hsum : ∑ i, α i = ∑ i ∈ T, c i / (f T - f (T.erase i)) := by
    simp [α]
  have hpu : principalUtility f α T = (1 - ∑ i ∈ T, c i / (f T - f (T.erase i))) * f T := by
    simp [principalUtility, hsum]
  rw [← hpu]
  exact le_V_of_isEquilibrium hf hα heq

/-! ### Section 2: Submodularity & The Potential Lemma (Lemma 4.2) -/

lemma submod_erase_le {n : ℕ} {f : Finset (Fin n) → ℝ}
    (hsub : SubsamplingSM.Offline.IsSubmodular f)
    {T T' : Finset (Fin n)} (hTT' : T ⊆ T') {i : Fin n} (hi : i ∈ T) :
    f T' - f (T'.erase i) ≤ f T - f (T.erase i) := by
  have hi' : i ∈ T' := hTT' hi
  have hsub_erase : T.erase i ⊆ T'.erase i := erase_subset_erase i hTT'
  have hni : i ∉ T'.erase i := by simp
  have h := hsub (T.erase i) (T'.erase i) i hsub_erase hni
  rwa [insert_erase hi', insert_erase hi] at h

lemma sum_teamMarginal_le {n : ℕ} {f : Finset (Fin n) → ℝ}
    (hsub : SubsamplingSM.Offline.IsSubmodular f) (S : Finset (Fin n)) :
    ∑ i ∈ S, (f S - f (S.erase i)) ≤ f S - f ∅ := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    rw [sum_insert ha, erase_insert ha]
    have hle : ∑ i ∈ S, (f (insert a S) - f ((insert a S).erase i)) ≤
        ∑ i ∈ S, (f S - f (S.erase i)) :=
      sum_le_sum (fun i hi => submod_erase_le hsub (subset_insert a S) hi)
    linarith

noncomputable def potentialPhi {n : ℕ} (f : Finset (Fin n) → ℝ) (d κ p : Fin n → ℝ)
    (B : ℝ) (T R : Finset (Fin n)) : ℝ :=
  B * (f T - (1 / 4 : ℝ) * ∑ j ∈ R, d j) + ∑ j ∈ R, κ j * (p j - d j)

lemma le_max_of_convex {a b c t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (h : c ≤ t * a + (1 - t) * b) : c ≤ max a b := by
  rcases le_total a b with hab | hba
  · rw [max_eq_right hab]
    nlinarith
  · rw [max_eq_left hba]
    nlinarith

lemma pruning_base {n : ℕ} {f : Finset (Fin n) → ℝ} (hf : IsSuccess f)
    {c : Fin n → ℝ} (hc : ∀ i, 0 ≤ c i)
    {S : Finset (Fin n)} (hcS : ∀ i ∈ S, 0 < c i)
    {κ : Fin n → ℝ} (hκS : ∀ i ∈ S, 0 < κ i)
    (H L : Finset (Fin n)) (ms : Fin n → ℝ)
    (hSub : H ∪ L ⊆ S) (hHL : Disjoint H L)
    (hB : 0 ≤ 1 - (∑ h ∈ H, κ h) - (∑ l ∈ L, c l / ms l))
    (hH : ∀ h ∈ H, c h / κ h ≤ ms h ∧ ms h ≤ f (H ∪ L) - f ((H ∪ L).erase h))
    (hL : ∀ l ∈ L, 0 < ms l ∧ ms l ≤ f (H ∪ L) - f ((H ∪ L).erase l)) :
    (∑ h ∈ H, κ h * (ms h - c h / κ h)) +
      max (potentialPhi f (fun i => c i / κ i) κ (fun i => f S - f (S.erase i))
        (1 - (∑ h ∈ H, κ h) - (∑ l ∈ L, c l / ms l)) (H ∪ L) ∅) 0 ≤ V f c := by
  let d : Fin n → ℝ := fun i => c i / κ i
  have hd_pos : ∀ i ∈ S, 0 < d i := fun i hi => div_pos (hcS i hi) (hκS i hi)
  have hκd : ∀ i ∈ S, κ i * d i = c i := fun i hi =>
    mul_div_cancel₀ (c i) (ne_of_gt (hκS i hi))
  let T := H ∪ L
  let B := 1 - (∑ h ∈ H, κ h) - (∑ l ∈ L, c l / ms l)
  let mb : Fin n → ℝ := fun i => f T - f (T.erase i)
  have hPhi : potentialPhi f d κ (fun i => f S - f (S.erase i)) B T ∅ = B * f T := by
    simp [potentialPhi]
  have hBT_nonneg : 0 ≤ B * f T := mul_nonneg hB (hf.2 T).1
  change (∑ h ∈ H, κ h * (ms h - d h)) +
    max (potentialPhi f d κ (fun i => f S - f (S.erase i)) B T ∅) 0 ≤ V f c
  rw [hPhi, max_eq_left hBT_nonneg]
  have hH_sub : H ⊆ S := Subset.trans subset_union_left hSub
  have hm_pos : ∀ i ∈ T, 0 < mb i := by
    intro i hi
    rcases mem_union.mp hi with hiH | hiL
    · have hd_hi := hd_pos i (hH_sub hiH)
      have ⟨h1, h2⟩ := hH i hiH
      dsimp [d] at hd_hi
      linarith
    · have ⟨h1, h2⟩ := hL i hiL
      linarith
  have hH_le : ∀ h ∈ H, c h / mb h ≤ κ h := by
    intro h hh
    have hhS := hH_sub hh
    have hmb_pos : 0 < mb h := hm_pos h (mem_union_left L hh)
    rw [div_le_iff₀ hmb_pos, ← hκd h hhS]
    have ⟨h1, h2⟩ := hH h hh
    exact mul_le_mul_of_nonneg_left (le_trans h1 h2) (le_of_lt (hκS h hhS))
  have hL_le : ∀ l ∈ L, c l / mb l ≤ c l / ms l := by
    intro l hl
    have ⟨h1, h2⟩ := hL l hl
    exact div_le_div_of_nonneg_left (hc l) h1 h2
  have h1_sub : 1 - ∑ i ∈ T, c i / mb i =
      B + (∑ h ∈ H, (κ h - c h / mb h)) + (∑ l ∈ L, (c l / ms l - c l / mb l)) := by
    rw [sum_union hHL]
    simp only [B, sum_sub_distrib]
    ring
  have hrem_nonneg : 0 ≤ 1 - ∑ i ∈ T, c i / mb i := by
    rw [h1_sub]
    have s1 : 0 ≤ ∑ h ∈ H, (κ h - c h / mb h) :=
      sum_nonneg (fun h hh => sub_nonneg.mpr (hH_le h hh))
    have s2 : 0 ≤ ∑ l ∈ L, (c l / ms l - c l / mb l) :=
      sum_nonneg (fun l hl => sub_nonneg.mpr (hL_le l hl))
    linarith
  have hm_le_one : ∀ i ∈ T, c i / mb i ≤ 1 := by
    intro i hi
    have hsingle : c i / mb i ≤ ∑ j ∈ T, c j / mb j :=
      single_le_sum (fun j hj => div_nonneg (hc j) (le_of_lt (hm_pos j hj))) hi
    linarith
  have hV := le_V_of_team hf hc T hm_pos hm_le_one
  have hH_term : ∀ h ∈ H, κ h * (ms h - d h) ≤ (κ h - c h / mb h) * f T := by
    intro h hh
    have hhS := hH_sub hh
    have hmb_pos : 0 < mb h := hm_pos h (mem_union_left L hh)
    have hmb_le_fT : mb h ≤ f T := by
      have := (hf.2 (T.erase h)).1
      dsimp [mb]
      linarith
    have hdiff_nonneg : 0 ≤ κ h - c h / mb h := sub_nonneg.mpr (hH_le h hh)
    have hmul1 : (κ h - c h / mb h) * mb h ≤ (κ h - c h / mb h) * f T :=
      mul_le_mul_of_nonneg_left hmb_le_fT hdiff_nonneg
    have heq_mb : (κ h - c h / mb h) * mb h = κ h * (mb h - d h) := by
      have hne : mb h ≠ 0 := ne_of_gt hmb_pos
      calc
        (κ h - c h / mb h) * mb h = κ h * mb h - (c h / mb h) * mb h := by ring
        _ = κ h * mb h - c h := by rw [div_mul_cancel₀ _ hne]
        _ = κ h * mb h - κ h * d h := by rw [hκd h hhS]
        _ = κ h * (mb h - d h) := by ring
    have ⟨_, hms_le⟩ := hH h hh
    have hmul2 : κ h * (ms h - d h) ≤ κ h * (mb h - d h) :=
      mul_le_mul_of_nonneg_left (by linarith) (le_of_lt (hκS h hhS))
    linarith
  have hsum_H_term : ∑ h ∈ H, κ h * (ms h - d h) ≤ ∑ h ∈ H, (κ h - c h / mb h) * f T :=
    sum_le_sum hH_term
  have hsum_L_nonneg : 0 ≤ (∑ l ∈ L, (c l / ms l - c l / mb l)) * f T :=
    mul_nonneg (sum_nonneg (fun l hl => sub_nonneg.mpr (hL_le l hl))) (hf.2 T).1
  have hexpand : (1 - ∑ i ∈ T, c i / mb i) * f T =
      B * f T + (∑ h ∈ H, (κ h - c h / mb h) * f T) +
        (∑ l ∈ L, (c l / ms l - c l / mb l)) * f T := by
    rw [h1_sub]
    simp only [add_mul, sum_mul]
  linarith

lemma pruning_step_algebra_case2 {B κi di pi ci mi X Y : ℝ}
    (hB : 0 ≤ B) (hκi : 0 < κi) (hdi : 0 < di) (hmi : 0 < mi)
    (hcieq : κi * di = ci) (hpi : pi ≤ mi)
    (ht0 : 0 < mi / di) (ht1 : mi / di < 1) :
    B * (X - di / 4) + κi * (pi - di) + Y ≤
      max ((B + κi - ci / mi) * X + Y) ((B + κi) * (X - (mi / di) * di) + Y) := by
  let t := mi / di
  have hmi_eq : t * di = mi := div_mul_cancel₀ mi (ne_of_gt hdi)
  have ht_cm : t * (ci / mi) = κi := by
    have hmi_ne : mi ≠ 0 := ne_of_gt hmi
    have hdi_ne : di ≠ 0 := ne_of_gt hdi
    dsimp [t]
    rw [← hcieq]
    field_simp
  have hid :
      t * ((B + κi - ci / mi) * X + Y) + (1 - t) * ((B + κi) * (X - t * di) + Y) -
        (B * (X - di / 4) + κi * (pi - di) + Y) =
      B * di * (t - 1 / 2) ^ 2 + κi * (di * (1 - t) ^ 2 + (t * di - pi)) := by
    calc
      t * ((B + κi - ci / mi) * X + Y) + (1 - t) * ((B + κi) * (X - t * di) + Y) -
          (B * (X - di / 4) + κi * (pi - di) + Y)
        = (t * (B + κi) - t * (ci / mi)) * X + t * Y +
            (1 - t) * ((B + κi) * (X - t * di) + Y) -
            (B * (X - di / 4) + κi * (pi - di) + Y) := by ring
      _ = (t * (B + κi) - κi) * X + t * Y +
            (1 - t) * ((B + κi) * (X - t * di) + Y) -
            (B * (X - di / 4) + κi * (pi - di) + Y) := by rw [ht_cm]
      _ = B * di * (t - 1 / 2) ^ 2 + κi * (di * (1 - t) ^ 2 + (t * di - pi)) := by ring
  have hge : B * (X - di / 4) + κi * (pi - di) + Y ≤
      t * ((B + κi - ci / mi) * X + Y) + (1 - t) * ((B + κi) * (X - t * di) + Y) := by
    have hs1 : 0 ≤ B * di * (t - 1 / 2) ^ 2 :=
      mul_nonneg (mul_nonneg hB (le_of_lt hdi)) (sq_nonneg _)
    have hs2 : 0 ≤ κi * (di * (1 - t) ^ 2 + (t * di - pi)) :=
      mul_nonneg (le_of_lt hκi) (add_nonneg (mul_nonneg (le_of_lt hdi) (sq_nonneg _)) (by linarith))
    linarith
  exact le_max_of_convex (le_of_lt ht0) (le_of_lt ht1) hge

lemma pruning_step_algebra_case3 {B κi di pi t X Y : ℝ}
    (hB : 0 ≤ B) (hκi : 0 < κi) (hdi : 0 < di) (ht1 : t < 1)
    (hpi : pi ≤ t * di) (hunaff : B * t < κi * (1 - t)) (hY : Y ≤ 0) :
    max (B * (X - di / 4) + κi * (pi - di) + Y) 0 ≤
      max ((B + κi) * (X - t * di) + Y) 0 := by
  let Pcur := B * (X - di / 4) + κi * (pi - di) + Y
  let Pdel := (B + κi) * (X - t * di) + Y
  rcases le_or_gt Pcur 0 with hnonpos | hpos
  · rw [max_eq_right hnonpos]
    exact le_max_right _ _
  · refine max_le_max_right 0 ?_
    have hdi_sub_pi : di * (1 - t) ≤ di - pi := by linarith
    have hdi_pi_pos : 0 < di - pi := by nlinarith
    have hBX_gt : κi * (di - pi) < B * (X - di / 4) := by
      dsimp [Pcur] at hpos
      linarith
    have hBX_pos : 0 < B * (X - di / 4) := lt_trans (mul_pos hκi hdi_pi_pos) hBX_gt
    have hB_pos : 0 < B := by
      rcases eq_or_lt_of_le hB with hB0 | hBp
      · rw [← hB0, zero_mul] at hBX_pos
        exact False.elim (lt_irrefl 0 hBX_pos)
      · exact hBp
    have hdiff_id :
        B * (Pdel - Pcur) =
          κi * (B * (X - di / 4) - κi * (di - pi)) +
            (B + κi) * (B * di / 4 - B * t * di + κi * (di - pi)) := by
      dsimp [Pdel, Pcur]
      ring
    have hterm1_pos : 0 < κi * (B * (X - di / 4) - κi * (di - pi)) :=
      mul_pos hκi (sub_pos.mpr hBX_gt)
    have hterm2_pos : 0 < (B + κi) * (B * di / 4 - B * t * di + κi * (di - pi)) := by
      refine mul_pos (by linarith) ?_
      have h1 : κi * (di * (1 - t)) ≤ κi * (di - pi) :=
        mul_le_mul_of_nonneg_left hdi_sub_pi (le_of_lt hκi)
      have h2 : B * t * di < κi * (1 - t) * di := mul_lt_mul_of_pos_right hunaff hdi
      have h3 : 0 < B * di / 4 := by positivity
      nlinarith
    have hBPdiff_pos : 0 < B * (Pdel - Pcur) := by linarith
    by_contra hlt
    have hneg : B * (Pdel - Pcur) < 0 :=
      mul_neg_of_pos_of_neg hB_pos (sub_neg.mpr (lt_of_not_ge hlt))
    linarith

lemma pruning_induction {n : ℕ} {f : Finset (Fin n) → ℝ}
    (hf : IsSuccess f) (hsub : SubsamplingSM.Offline.IsSubmodular f)
    {c : Fin n → ℝ} (hc : ∀ i, 0 ≤ c i)
    {S : Finset (Fin n)} (hcS : ∀ i ∈ S, 0 < c i)
    {κ : Fin n → ℝ} (hκS : ∀ i ∈ S, 0 < κ i) :
    ∀ (N : ℕ) (H L R : Finset (Fin n)) (ms : Fin n → ℝ),
      R.card = N →
      H ∪ L ∪ R ⊆ S →
      Disjoint H L → Disjoint H R → Disjoint L R →
      0 ≤ 1 - (∑ h ∈ H, κ h) - (∑ l ∈ L, c l / ms l) - (∑ j ∈ R, κ j) →
      (∀ h ∈ H, c h / κ h ≤ ms h ∧ ms h ≤ f (H ∪ L ∪ R) - f ((H ∪ L ∪ R).erase h)) →
      (∀ l ∈ L, 0 < ms l ∧ ms l ≤ f (H ∪ L ∪ R) - f ((H ∪ L ∪ R).erase l)) →
      (∑ h ∈ H, κ h * (ms h - c h / κ h)) +
        max (potentialPhi f (fun i => c i / κ i) κ (fun i => f S - f (S.erase i))
          (1 - (∑ h ∈ H, κ h) - (∑ l ∈ L, c l / ms l) - (∑ j ∈ R, κ j))
          (H ∪ L ∪ R) R) 0 ≤ V f c := by
  let d : Fin n → ℝ := fun i => c i / κ i
  let p : Fin n → ℝ := fun i => f S - f (S.erase i)
  have hd_pos : ∀ i ∈ S, 0 < d i := fun i hi => div_pos (hcS i hi) (hκS i hi)
  have hκd : ∀ i ∈ S, κ i * d i = c i := fun i hi =>
    mul_div_cancel₀ (c i) (ne_of_gt (hκS i hi))
  intro N
  induction N with
  | zero =>
    intro H L R ms hRcard hSub hHL _ _ hB hH hL
    have hR : R = ∅ := card_eq_zero.mp hRcard
    subst hR
    simp only [union_empty, sum_empty, sub_zero] at hSub hB hH hL ⊢
    exact pruning_base hf hc hcS hκS H L ms hSub hHL hB hH hL
  | succ N ih =>
    intro H L R ms hRcard hSub hHL hHR hLR hB hH hL
    change (∑ h ∈ H, κ h * (ms h - d h)) +
      max (potentialPhi f d κ p
        (1 - (∑ h ∈ H, κ h) - (∑ l ∈ L, c l / ms l) - (∑ j ∈ R, κ j))
        (H ∪ L ∪ R) R) 0 ≤ V f c
    let T := H ∪ L ∪ R
    let B := 1 - (∑ h ∈ H, κ h) - (∑ l ∈ L, c l / ms l) - (∑ j ∈ R, κ j)
    have hR_ne : R.Nonempty := card_pos.mp (by omega)
    obtain ⟨i, hiR, himax⟩ :=
      exists_max_image R (fun j => (f T - f (T.erase j)) / d j) hR_ne
    let R' := R.erase i
    have hR'card : R'.card = N := by
      dsimp [R']
      have hce := card_erase_of_mem hiR
      omega
    have hiR' : i ∉ R' := by simp [R']
    have hinsR' : insert i R' = R := insert_erase hiR
    have hiT : i ∈ T := mem_union_right (H ∪ L) hiR
    have hiS : i ∈ S := hSub hiT
    have hdi_pos : 0 < d i := hd_pos i hiS
    have hκi_pos : 0 < κ i := hκS i hiS
    have hci_eq : κ i * d i = c i := hκd i hiS
    have hiH : i ∉ H := disjoint_right.mp hHR hiR
    have hiL : i ∉ L := disjoint_right.mp hLR hiR
    let mi := f T - f (T.erase i)
    let t := mi / d i
    have hmi_nonneg : 0 ≤ mi := sub_nonneg.mpr (hf.1 (erase_subset i T))
    have ht_nonneg : 0 ≤ t := div_nonneg hmi_nonneg (le_of_lt hdi_pos)
    have hmi_eq : mi = t * d i := (div_mul_cancel₀ mi (ne_of_gt hdi_pos)).symm
    have hpi_le : p i ≤ mi := submod_erase_le hsub hSub hiT
    let X := f T - (1 / 4 : ℝ) * ∑ j ∈ R', d j
    let Y := ∑ j ∈ R', κ j * (p j - d j)
    have hPhi_cur : potentialPhi f d κ p B T R =
        B * (X - d i / 4) + κ i * (p i - d i) + Y := by
      unfold potentialPhi
      rw [← hinsR', sum_insert hiR', sum_insert hiR']
      dsimp [X, Y]
      ring
    -- Helper: deletion step applies IH to (H, L, R', ms)
    have h_del_step :
        (∑ h ∈ H, κ h * (ms h - d h)) +
          max ((B + κ i) * (X - t * d i) + Y) 0 ≤ V f c := by
      have hT_del : H ∪ L ∪ R' = T.erase i := by
        ext x
        by_cases hx : x = i
        · subst hx
          simp [T, R', hiH, hiL]
        · simp [T, R', hx]
      have hSub_del : H ∪ L ∪ R' ⊆ S := by
        rw [hT_del]
        exact Subset.trans (erase_subset i T) hSub
      have hHR' : Disjoint H R' := Disjoint.mono_right (erase_subset i R) hHR
      have hLR' : Disjoint L R' := Disjoint.mono_right (erase_subset i R) hLR
      have hB_del_eq :
          1 - (∑ h ∈ H, κ h) - (∑ l ∈ L, c l / ms l) - (∑ j ∈ R', κ j) = B + κ i := by
        dsimp [B]
        rw [← hinsR', sum_insert hiR']
        ring
      have hB_del : 0 ≤ 1 - (∑ h ∈ H, κ h) - (∑ l ∈ L, c l / ms l) - (∑ j ∈ R', κ j) := by
        rw [hB_del_eq]
        linarith
      have hH_del : ∀ h ∈ H, c h / κ h ≤ ms h ∧
          ms h ≤ f (H ∪ L ∪ R') - f ((H ∪ L ∪ R').erase h) := by
        intro h hh
        rw [hT_del]
        have ⟨h1, h2⟩ := hH h hh
        have hh_ne : h ≠ i := fun heq => hiH (heq ▸ hh)
        have hh_mem : h ∈ T.erase i := mem_erase.mpr ⟨hh_ne, mem_union_left R (mem_union_left L hh)⟩
        exact ⟨h1, le_trans h2 (submod_erase_le hsub (erase_subset i T) hh_mem)⟩
      have hL_del : ∀ l ∈ L, 0 < ms l ∧
          ms l ≤ f (H ∪ L ∪ R') - f ((H ∪ L ∪ R').erase l) := by
        intro l hl
        rw [hT_del]
        have ⟨h1, h2⟩ := hL l hl
        have hl_ne : l ≠ i := fun heq => hiL (heq ▸ hl)
        have hl_mem : l ∈ T.erase i := mem_erase.mpr ⟨hl_ne, mem_union_left R (mem_union_right H hl)⟩
        exact ⟨h1, le_trans h2 (submod_erase_le hsub (erase_subset i T) hl_mem)⟩
      have hih := ih H L R' ms hR'card hSub_del hHL hHR' hLR' hB_del hH_del hL_del
      change (∑ h ∈ H, κ h * (ms h - d h)) +
        max (potentialPhi f d κ p
          (1 - (∑ h ∈ H, κ h) - (∑ l ∈ L, c l / ms l) - (∑ j ∈ R', κ j))
          (H ∪ L ∪ R') R') 0 ≤ V f c at hih
      have hPhi_del : potentialPhi f d κ p (B + κ i) (H ∪ L ∪ R') R' =
          (B + κ i) * (X - t * d i) + Y := by
        rw [hT_del]
        unfold potentialPhi
        have hf_erase : f (T.erase i) = f T - t * d i := by
          dsimp [mi] at hmi_eq
          linarith
        rw [hf_erase]
        dsimp [X, Y]
        ring
      rwa [hB_del_eq, hPhi_del] at hih
    -- Case 1: t ≥ 1 (keep i as a high agent)
    by_cases ht1 : 1 ≤ t
    · let H' := insert i H
      let ms' := Function.update ms i mi
      have hT_high : H' ∪ L ∪ R' = T := by
        ext x
        by_cases hx : x = i <;> simp [H', R', T, hx, hiR]
      have hSub' : H' ∪ L ∪ R' ⊆ S := hT_high.symm ▸ hSub
      have hHL' : Disjoint H' L := disjoint_insert_left.mpr ⟨hiL, hHL⟩
      have hHR' : Disjoint H' R' :=
        disjoint_insert_left.mpr ⟨hiR', Disjoint.mono_right (erase_subset i R) hHR⟩
      have hLR' : Disjoint L R' := Disjoint.mono_right (erase_subset i R) hLR
      have hsumL_ms' : ∑ l ∈ L, c l / ms' l = ∑ l ∈ L, c l / ms l :=
        sum_congr rfl (fun l hl => by
          have hl_ne : l ≠ i := fun heq => hiL (heq ▸ hl)
          simp [ms', Function.update_of_ne hl_ne])
      have hB_eq :
          1 - (∑ h ∈ H', κ h) - (∑ l ∈ L, c l / ms' l) - (∑ j ∈ R', κ j) = B := by
        rw [hsumL_ms']
        dsimp [H', B]
        rw [sum_insert hiH, ← hinsR', sum_insert hiR']
        ring
      have hB' : 0 ≤ 1 - (∑ h ∈ H', κ h) - (∑ l ∈ L, c l / ms' l) - (∑ j ∈ R', κ j) :=
        hB_eq.symm ▸ hB
      have hdi_le_mi : d i ≤ mi := by
        rw [hmi_eq]
        nlinarith
      have hH' : ∀ h ∈ H', c h / κ h ≤ ms' h ∧
          ms' h ≤ f (H' ∪ L ∪ R') - f ((H' ∪ L ∪ R').erase h) := by
        intro h hh
        rw [hT_high]
        rcases mem_insert.mp hh with rfl | hhH
        · rw [show ms' h = mi from Function.update_self h mi ms]
          exact ⟨hdi_le_mi, le_refl _⟩
        · have hh_ne : h ≠ i := fun heq => hiH (heq ▸ hhH)
          rw [show ms' h = ms h from Function.update_of_ne hh_ne mi ms]
          exact hH h hhH
      have hL' : ∀ l ∈ L, 0 < ms' l ∧
          ms' l ≤ f (H' ∪ L ∪ R') - f ((H' ∪ L ∪ R').erase l) := by
        intro l hl
        rw [hT_high]
        have hl_ne : l ≠ i := fun heq => hiL (heq ▸ hl)
        rw [show ms' l = ms l from Function.update_of_ne hl_ne mi ms]
        exact hL l hl
      have hih := ih H' L R' ms' hR'card hSub' hHL' hHR' hLR' hB' hH' hL'
      change (∑ h ∈ H', κ h * (ms' h - d h)) +
        max (potentialPhi f d κ p
          (1 - (∑ h ∈ H', κ h) - (∑ l ∈ L, c l / ms' l) - (∑ j ∈ R', κ j))
          (H' ∪ L ∪ R') R') 0 ≤ V f c at hih
      rw [hB_eq, hT_high] at hih
      have hQ' : ∑ h ∈ H', κ h * (ms' h - d h) =
          (∑ h ∈ H, κ h * (ms h - d h)) + κ i * (mi - d i) := by
        dsimp [H']
        rw [sum_insert hiH]
        have hrest : ∑ h ∈ H, κ h * (ms' h - d h) = ∑ h ∈ H, κ h * (ms h - d h) :=
          sum_congr rfl (fun h hh => by
            have hh_ne : h ≠ i := fun heq => hiH (heq ▸ hh)
            simp [ms', Function.update_of_ne hh_ne])
        rw [hrest, show ms' i = mi from Function.update_self i mi ms]
        ring
      have hPhi' : potentialPhi f d κ p B T R' = B * X + Y := by
        simp [potentialPhi, X, Y]
      rw [hQ', hPhi'] at hih
      rw [hPhi_cur]
      have hle_max :
          (∑ h ∈ H, κ h * (ms h - d h)) + max (B * (X - d i / 4) + κ i * (p i - d i) + Y) 0 ≤
          (∑ h ∈ H, κ h * (ms h - d h)) + κ i * (mi - d i) + max (B * X + Y) 0 := by
        rcases le_total (B * (X - d i / 4) + κ i * (p i - d i) + Y) 0 with hneg | hpos
        · rw [max_eq_right hneg]
          have h1 : 0 ≤ κ i * (mi - d i) := mul_nonneg (le_of_lt hκi_pos) (by linarith)
          have h2 : 0 ≤ max (B * X + Y) 0 := le_max_right _ _
          linarith
        · rw [max_eq_left hpos]
          have h2 : B * X + Y ≤ max (B * X + Y) 0 := le_max_left _ _
          have h3 : 0 ≤ B * (d i / 4) := mul_nonneg hB (by positivity)
          have h4 : 0 ≤ κ i * (mi - p i) := mul_nonneg (le_of_lt hκi_pos) (by linarith)
          linarith
      exact le_trans hle_max hih
    · have ht_lt1 : t < 1 := lt_of_not_ge ht1
      by_cases haff : 0 < t ∧ 0 ≤ B + κ i - c i / mi
      · rcases haff with ⟨ht_pos, hB_keep⟩
        have hmi_pos : 0 < mi := by
          rw [hmi_eq]
          exact mul_pos ht_pos hdi_pos
        have h_keep_step :
            (∑ h ∈ H, κ h * (ms h - d h)) +
              max ((B + κ i - c i / mi) * X + Y) 0 ≤ V f c := by
          let L' := insert i L
          let ms' := Function.update ms i mi
          have hT_keep : H ∪ L' ∪ R' = T := by
            ext x
            by_cases hx : x = i <;> simp [L', R', T, hx, hiR]
          have hSub' : H ∪ L' ∪ R' ⊆ S := hT_keep.symm ▸ hSub
          have hHL' : Disjoint H L' := disjoint_insert_right.mpr ⟨hiH, hHL⟩
          have hHR' : Disjoint H R' := Disjoint.mono_right (erase_subset i R) hHR
          have hLR' : Disjoint L' R' :=
            disjoint_insert_left.mpr ⟨hiR', Disjoint.mono_right (erase_subset i R) hLR⟩
          have hsumL'_ms' : ∑ l ∈ L', c l / ms' l = c i / mi + ∑ l ∈ L, c l / ms l := by
            dsimp [L']
            rw [sum_insert hiL]
            have hrest : ∑ l ∈ L, c l / ms' l = ∑ l ∈ L, c l / ms l :=
              sum_congr rfl (fun l hl => by
                have hl_ne : l ≠ i := fun heq => hiL (heq ▸ hl)
                simp [ms', Function.update_of_ne hl_ne])
            rw [hrest, show ms' i = mi from Function.update_self i mi ms]
          have hB_eq :
              1 - (∑ h ∈ H, κ h) - (∑ l ∈ L', c l / ms' l) - (∑ j ∈ R', κ j) =
                B + κ i - c i / mi := by
            rw [hsumL'_ms']
            dsimp [B]
            rw [← hinsR', sum_insert hiR']
            ring
          have hB' : 0 ≤ 1 - (∑ h ∈ H, κ h) - (∑ l ∈ L', c l / ms' l) - (∑ j ∈ R', κ j) :=
            hB_eq.symm ▸ hB_keep
          have hH' : ∀ h ∈ H, c h / κ h ≤ ms' h ∧
              ms' h ≤ f (H ∪ L' ∪ R') - f ((H ∪ L' ∪ R').erase h) := by
            intro h hh
            rw [hT_keep]
            have hh_ne : h ≠ i := fun heq => hiH (heq ▸ hh)
            rw [show ms' h = ms h from Function.update_of_ne hh_ne mi ms]
            exact hH h hh
          have hL' : ∀ l ∈ L', 0 < ms' l ∧
              ms' l ≤ f (H ∪ L' ∪ R') - f ((H ∪ L' ∪ R').erase l) := by
            intro l hl
            rw [hT_keep]
            rcases mem_insert.mp hl with rfl | hlL
            · rw [show ms' l = mi from Function.update_self l mi ms]
              exact ⟨hmi_pos, le_refl _⟩
            · have hl_ne : l ≠ i := fun heq => hiL (heq ▸ hlL)
              rw [show ms' l = ms l from Function.update_of_ne hl_ne mi ms]
              exact hL l hlL
          have hih := ih H L' R' ms' hR'card hSub' hHL' hHR' hLR' hB' hH' hL'
          change (∑ h ∈ H, κ h * (ms' h - d h)) +
            max (potentialPhi f d κ p
              (1 - (∑ h ∈ H, κ h) - (∑ l ∈ L', c l / ms' l) - (∑ j ∈ R', κ j))
              (H ∪ L' ∪ R') R') 0 ≤ V f c at hih
          rw [hB_eq, hT_keep] at hih
          have hQ' : ∑ h ∈ H, κ h * (ms' h - d h) = ∑ h ∈ H, κ h * (ms h - d h) :=
            sum_congr rfl (fun h hh => by
              have hh_ne : h ≠ i := fun heq => hiH (heq ▸ hh)
              simp [ms', Function.update_of_ne hh_ne])
          have hPhi' : potentialPhi f d κ p (B + κ i - c i / mi) T R' =
              (B + κ i - c i / mi) * X + Y := by
            simp [potentialPhi, X, Y]
          rwa [hQ', hPhi'] at hih
        have hcase2 := pruning_step_algebra_case2 (X := X) (Y := Y)
          hB hκi_pos hdi_pos hmi_pos hci_eq hpi_le ht_pos ht_lt1
        rw [hPhi_cur]
        rcases le_total ((B + κ i) * (X - t * d i) + Y) ((B + κ i - c i / mi) * X + Y) with hcmp | hcmp
        · rw [max_eq_left hcmp] at hcase2
          have hmax_le := max_le_max_right 0 hcase2
          linarith
        · rw [max_eq_right hcmp] at hcase2
          have hmax_le := max_le_max_right 0 hcase2
          linarith
      · -- Case 3: keeping i is unaffordable; delete i
        rw [hPhi_cur]
        have hunaff : B * t < κ i * (1 - t) := by
          rcases eq_or_lt_of_le ht_nonneg with ht0 | ht_pos
          · rw [← ht0]
            nlinarith
          · have hnot : B + κ i - c i / mi < 0 := by
              by_contra hge
              exact haff ⟨ht_pos, le_of_not_gt hge⟩
            have hmi_pos : 0 < mi := by
              rw [hmi_eq]
              exact mul_pos ht_pos hdi_pos
            have ht_cm : t * (c i / mi) = κ i := by
              have hmi_ne : mi ≠ 0 := ne_of_gt hmi_pos
              have hdi_ne : d i ≠ 0 := ne_of_gt hdi_pos
              dsimp [t]
              rw [← hci_eq]
              field_simp
            have hmul : t * (B + κ i - c i / mi) < 0 := mul_neg_of_pos_of_neg ht_pos hnot
            nlinarith
        have hY_nonpos : Y ≤ 0 := by
          refine sum_nonpos (fun j hj => ?_)
          have hjR : j ∈ R := mem_of_mem_erase hj
          have hjT : j ∈ T := mem_union_right (H ∪ L) hjR
          have hjS : j ∈ S := hSub hjT
          have hdj_pos : 0 < d j := hd_pos j hjS
          have hκj_pos : 0 < κ j := hκS j hjS
          have hrat : (f T - f (T.erase j)) / d j ≤ t := himax j hjR
          have hmj_lt : f T - f (T.erase j) < d j := by
            have := (div_le_iff₀ hdj_pos).mp hrat
            nlinarith
          have hpj_le : p j ≤ f T - f (T.erase j) := submod_erase_le hsub hSub hjT
          exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt hκj_pos) (by linarith)
        have hpi_le_tdi : p i ≤ t * d i := hmi_eq ▸ hpi_le
        have hcase3 := pruning_step_algebra_case3 (X := X) hB hκi_pos hdi_pos
          ht_lt1 hpi_le_tdi hunaff hY_nonpos
        linarith

/-- Lemma 4.2 (Potential Lemma). -/
lemma potential_lemma {n : ℕ} {f : Finset (Fin n) → ℝ}
    (hf : IsSuccess f) (hsub : SubsamplingSM.Offline.IsSubmodular f)
    {c : Fin n → ℝ} (hc : ∀ i, 0 ≤ c i)
    (S : Finset (Fin n)) (hcS : ∀ i ∈ S, 0 < c i)
    (κ : Fin n → ℝ) (hκS : ∀ i ∈ S, 0 < κ i) (hκ_sum : ∑ i ∈ S, κ i ≤ 1) :
    (1 - ∑ i ∈ S, κ i) * (f S - (1 / 4 : ℝ) * ∑ i ∈ S, c i / κ i) +
      ∑ i ∈ S, κ i * ((f S - f (S.erase i)) - c i / κ i) ≤ V f c := by
  have h := pruning_induction hf hsub hc hcS hκS S.card ∅ ∅ S (fun _ => 0)
    rfl (by simp) (by simp) (by simp) (by simp)
    (by simp; linarith) (by simp) (by simp)
  simp only [empty_union, sum_empty, zero_add, sub_zero] at h
  exact le_trans (le_max_left _ 0) h

/-! ### Section 3: Zero-Cost Folding & No-Info vs. Full-Info -/

lemma posteriorReward_isSuccess {n m : ℕ} (M : Model n m) (μ : Belief m) :
    IsSuccess (posteriorReward M μ) := by
  refine ⟨fun A B hAB => ?_, fun S => ⟨?_, ?_⟩⟩
  · exact sum_le_sum (fun ω _ => mul_le_mul_of_nonneg_left ((M.success ω).1 hAB) (μ.2.1 ω))
  · exact sum_nonneg (fun ω _ => mul_nonneg (μ.2.1 ω) ((M.success ω).2 S).1)
  · calc
      posteriorReward M μ S = ∑ ω, (μ : Fin m → ℝ) ω * M.f ω S := rfl
      _ ≤ ∑ ω, (μ : Fin m → ℝ) ω * 1 :=
        sum_le_sum (fun ω _ => mul_le_mul_of_nonneg_left ((M.success ω).2 S).2 (μ.2.1 ω))
      _ = 1 := by
        simp only [mul_one]
        exact μ.2.2

lemma posteriorReward_isSubmodular {n m : ℕ} (M : Model n m) (μ : Belief m)
    (hsub : ∀ ω, SubsamplingSM.Offline.IsSubmodular (M.f ω)) :
    SubsamplingSM.Offline.IsSubmodular (posteriorReward M μ) := by
  intro A B e hAB heB
  have h1 : posteriorReward M μ (insert e B) - posteriorReward M μ B =
      ∑ ω, (μ : Fin m → ℝ) ω * (M.f ω (insert e B) - M.f ω B) := by
    simp [posteriorReward, ← sum_sub_distrib, mul_sub]
  have h2 : posteriorReward M μ (insert e A) - posteriorReward M μ A =
      ∑ ω, (μ : Fin m → ℝ) ω * (M.f ω (insert e A) - M.f ω A) := by
    simp [posteriorReward, ← sum_sub_distrib, mul_sub]
  rw [h1, h2]
  exact sum_le_sum (fun ω _ => mul_le_mul_of_nonneg_left (hsub ω A B e hAB heB) (μ.2.1 ω))

lemma foldZero_isSuccess {n : ℕ} {f : Finset (Fin n) → ℝ} (hf : IsSuccess f)
    (Z : Finset (Fin n)) :
    IsSuccess (fun A => f (A ∪ Z)) :=
  ⟨fun _ _ hAB => hf.1 (union_subset_union hAB Subset.rfl), fun A => hf.2 (A ∪ Z)⟩

lemma foldZero_isSubmodular {n : ℕ} {f : Finset (Fin n) → ℝ}
    (hsub : SubsamplingSM.Offline.IsSubmodular f) (Z : Finset (Fin n)) :
    SubsamplingSM.Offline.IsSubmodular (fun A => f (A ∪ Z)) := by
  intro A B e hAB heB
  by_cases heZ : e ∈ Z
  · have hB : insert e B ∪ Z = B ∪ Z := by
      ext x
      by_cases hx : x = e <;> simp [hx, heZ]
    have hA : insert e A ∪ Z = A ∪ Z := by
      ext x
      by_cases hx : x = e <;> simp [hx, heZ]
    simp [hB, hA]
  · have heBZ : e ∉ B ∪ Z := by simp [heB, heZ]
    have hABZ : A ∪ Z ⊆ B ∪ Z := union_subset_union hAB Subset.rfl
    simpa [insert_union] using hsub (A ∪ Z) (B ∪ Z) e hABZ heBZ

lemma foldZero_V_le {n : ℕ} {f : Finset (Fin n) → ℝ} (hf : IsSuccess f)
    {c : Fin n → ℝ} (hc : ∀ i, 0 ≤ c i)
    (Z : Finset (Fin n)) (hcZ : ∀ i ∈ Z, c i = 0) :
    V (fun A => f (A ∪ Z)) c ≤ V f c := by
  refine csSup_le (statelessPayoffs_nonempty (fun A => f (A ∪ Z)) c hc) ?_
  rintro u ⟨α, A, hα, heq, rfl⟩
  rw [isEquilibrium_iff] at heq
  have heq' : IsEquilibrium f c α (A ∪ Z) := by
    rw [isEquilibrium_iff]
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · by_cases hiZ : i ∈ Z
      · rw [hcZ i hiZ]
        exact mul_nonneg (hα i (mem_univ i)).1
          (sub_nonneg.mpr (hf.1 (erase_subset i (A ∪ Z))))
      · have hiA : i ∈ A := by
          rcases mem_union.mp hi with hiA | hiZ'
          · exact hiA
          · exact False.elim (hiZ hiZ')
        have herase : A.erase i ∪ Z = (A ∪ Z).erase i := by
          ext x
          by_cases hx : x = i <;> simp [hx, hiZ]
        have h1 := heq.1 i hiA
        rwa [herase] at h1
    · have hiA : i ∉ A := fun h => hi (mem_union_left Z h)
      have h2 := heq.2 i hiA
      rwa [insert_union] at h2
  have hpu : principalUtility (fun B => f (B ∪ Z)) α A = principalUtility f α (A ∪ Z) := rfl
  rw [hpu]
  exact le_V_of_isEquilibrium hf hα heq'

lemma three_quarters_noInformation_le_fullInformation {n m : ℕ}
    (M : Model n m) (μ : Belief m)
    (hsub : ∀ ω, SubsamplingSM.Offline.IsSubmodular (M.f ω)) :
    (3 / 4 : ℝ) * noInformation M μ ≤ fullInformation M μ := by
  have hfμ : IsSuccess (posteriorReward M μ) := posteriorReward_isSuccess M μ
  have hsubμ : SubsamplingSM.Offline.IsSubmodular (posteriorReward M μ) :=
    posteriorReward_isSubmodular M μ hsub
  have hFI_nonneg : 0 ≤ fullInformation M μ :=
    sum_nonneg (fun ω _ => mul_nonneg (μ.2.1 ω) (V_nonneg (M.success ω) M.cost_nonneg))
  suffices hmain : ∀ u ∈ statelessPayoffs (posteriorReward M μ) M.c,
      u ≤ (4 / 3 : ℝ) * fullInformation M μ by
    have hsup := csSup_le (statelessPayoffs_nonempty _ M.c M.cost_nonneg) hmain
    unfold noInformation V
    linarith
  rintro u ⟨α, S, hα, heq, rfl⟩
  suffices hpu : (3 / 4 : ℝ) * principalUtility (posteriorReward M μ) α S ≤
      fullInformation M μ by linarith
  rcases le_or_gt (principalUtility (posteriorReward M μ) α S) 0 with hle0 | hpos
  · linarith
  · let fμ := posteriorReward M μ
    have hfμS_nonneg : 0 ≤ fμ S := (hfμ.2 S).1
    have h1_sub_α_pos : 0 < 1 - ∑ i, α i := by
      by_contra hle
      have : principalUtility fμ α S ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hle) hfμS_nonneg
      linarith
    let P := S.filter (fun i => 0 < M.c i)
    let Z := S.filter (fun i => M.c i = 0)
    have hPZ_disj : Disjoint P Z := by
      rw [disjoint_filter]
      intro i _ h1 h2
      linarith
    have hPZ_union : P ∪ Z = S := by
      ext i
      simp only [mem_union, mem_filter, P, Z]
      constructor
      · rintro (⟨hi, _⟩ | ⟨hi, _⟩) <;> exact hi
      · intro hi
        rcases eq_or_lt_of_le (M.cost_nonneg i) with hc0 | hcpos
        · exact Or.inr ⟨hi, hc0.symm⟩
        · exact Or.inl ⟨hi, hcpos⟩
    have hcP : ∀ i ∈ P, 0 < M.c i := fun i hi => (mem_filter.mp hi).2
    have hcZ : ∀ i ∈ Z, M.c i = 0 := fun i hi => (mem_filter.mp hi).2
    let d : Fin n → ℝ := fun i => fμ S - fμ (S.erase i)
    let κ : Fin n → ℝ := fun i => M.c i / d i
    rw [isEquilibrium_iff] at heq
    have hd_pos : ∀ i ∈ P, 0 < d i := by
      intro i hi
      have hiS : i ∈ S := (mem_filter.mp hi).1
      have hci_pos : 0 < M.c i := hcP i hi
      have h_ic : M.c i ≤ α i * d i := heq.1 i hiS
      have hα_nn : 0 ≤ α i := (hα i (mem_univ i)).1
      by_contra hd_le
      have : α i * d i ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hα_nn (le_of_not_gt hd_le)
      linarith
    have hκ_pos : ∀ i ∈ P, 0 < κ i := fun i hi => div_pos (hcP i hi) (hd_pos i hi)
    have hκ_le_α : ∀ i ∈ P, κ i ≤ α i := by
      intro i hi
      have hiS : i ∈ S := (mem_filter.mp hi).1
      exact (div_le_iff₀ (hd_pos i hi)).mpr (heq.1 i hiS)
    have hsum_κ_le_α : ∑ i ∈ P, κ i ≤ ∑ i, α i := by
      calc
        ∑ i ∈ P, κ i ≤ ∑ i ∈ P, α i := sum_le_sum hκ_le_α
        _ ≤ ∑ i ∈ univ, α i :=
          sum_le_univ_sum_of_nonneg (fun i => (hα i (mem_univ i)).1)
    have hsum_κ_le_one : ∑ i ∈ P, κ i ≤ 1 := by linarith
    have hc_div_κ : ∀ i ∈ P, M.c i / κ i = d i := by
      intro i hi
      have hci_ne : M.c i ≠ 0 := ne_of_gt (hcP i hi)
      have hdi_ne : d i ≠ 0 := ne_of_gt (hd_pos i hi)
      dsimp [κ]
      field_simp
    -- Apply Potential Lemma in every state ω to fZ ω
    have hstate : ∀ ω : Fin m,
        (1 - ∑ i ∈ P, κ i) * (M.f ω S - (1 / 4 : ℝ) * ∑ i ∈ P, d i) +
          ∑ i ∈ P, κ i * ((M.f ω S - M.f ω (S.erase i)) - d i) ≤ V (M.f ω) M.c := by
      intro ω
      let fZ : Finset (Fin n) → ℝ := fun A => M.f ω (A ∪ Z)
      have hfZ_succ : IsSuccess fZ := foldZero_isSuccess (M.success ω) Z
      have hfZ_sub : SubsamplingSM.Offline.IsSubmodular fZ := foldZero_isSubmodular (hsub ω) Z
      have hpot := potential_lemma hfZ_succ hfZ_sub M.cost_nonneg P hcP κ hκ_pos hsum_κ_le_one
      have hV_fold : V fZ M.c ≤ V (M.f ω) M.c := foldZero_V_le (M.success ω) M.cost_nonneg Z hcZ
      have hfZP : fZ P = M.f ω S := by simp [fZ, hPZ_union]
      have hd_eq : ∑ i ∈ P, M.c i / κ i = ∑ i ∈ P, d i :=
        sum_congr rfl (fun i hi => hc_div_κ i hi)
      have hcorr_eq :
          ∑ i ∈ P, κ i * ((fZ P - fZ (P.erase i)) - M.c i / κ i) =
            ∑ i ∈ P, κ i * ((M.f ω S - M.f ω (S.erase i)) - d i) := by
        refine sum_congr rfl (fun i hi => ?_)
        have hiZ : i ∉ Z := disjoint_left.mp hPZ_disj hi
        have herase : P.erase i ∪ Z = S.erase i := by
          rw [← hPZ_union]
          ext x
          by_cases hx : x = i <;> simp [hx, hiZ]
        simp [fZ, hPZ_union, herase, hc_div_κ i hi]
      rw [hcorr_eq, hfZP, hd_eq] at hpot
      exact le_trans hpot hV_fold
    -- Weight by μ ω and sum over ω
    have hweighted :
        ∑ ω : Fin m, (μ : Fin m → ℝ) ω *
          ((1 - ∑ i ∈ P, κ i) * (M.f ω S - (1 / 4 : ℝ) * ∑ i ∈ P, d i) +
            ∑ i ∈ P, κ i * ((M.f ω S - M.f ω (S.erase i)) - d i)) ≤
          fullInformation M μ :=
      sum_le_sum (fun ω _ => mul_le_mul_of_nonneg_left (hstate ω) (μ.2.1 ω))
    have hμ_sum1 : ∑ ω : Fin m, (μ : Fin m → ℝ) ω = 1 := μ.2.2
    have hterm1 :
        ∑ ω : Fin m, (μ : Fin m → ℝ) ω *
          ((1 - ∑ i ∈ P, κ i) * (M.f ω S - (1 / 4 : ℝ) * ∑ i ∈ P, d i)) =
          (1 - ∑ i ∈ P, κ i) * (fμ S - (1 / 4 : ℝ) * ∑ i ∈ P, d i) := by
      have h1 : ∀ ω : Fin m,
          (μ : Fin m → ℝ) ω * ((1 - ∑ i ∈ P, κ i) * (M.f ω S - (1 / 4 : ℝ) * ∑ i ∈ P, d i)) =
            (1 - ∑ i ∈ P, κ i) * ((μ : Fin m → ℝ) ω * M.f ω S) -
              (1 - ∑ i ∈ P, κ i) * ((1 / 4 : ℝ) * ∑ i ∈ P, d i) * (μ : Fin m → ℝ) ω := by
        intro ω; ring
      simp_rw [h1, sum_sub_distrib, ← mul_sum]
      dsimp [fμ, posteriorReward]
      rw [hμ_sum1]
      ring
    have hterm2 :
        ∑ ω : Fin m, (μ : Fin m → ℝ) ω *
          (∑ i ∈ P, κ i * ((M.f ω S - M.f ω (S.erase i)) - d i)) = 0 := by
      simp_rw [mul_sum]
      rw [sum_comm]
      refine sum_eq_zero (fun i _ => ?_)
      have h2 : ∀ ω : Fin m,
          (μ : Fin m → ℝ) ω * (κ i * ((M.f ω S - M.f ω (S.erase i)) - d i)) =
            κ i * ((μ : Fin m → ℝ) ω * M.f ω S - (μ : Fin m → ℝ) ω * M.f ω (S.erase i) -
              d i * (μ : Fin m → ℝ) ω) := by
        intro ω; ring
      simp_rw [h2, ← mul_sum, sum_sub_distrib, ← mul_sum]
      dsimp [d, fμ, posteriorReward]
      rw [hμ_sum1]
      ring
    have hFI_ge :
        (1 - ∑ i ∈ P, κ i) * (fμ S - (1 / 4 : ℝ) * ∑ i ∈ P, d i) ≤ fullInformation M μ := by
      have hsplit :
          ∑ ω : Fin m, (μ : Fin m → ℝ) ω *
            ((1 - ∑ i ∈ P, κ i) * (M.f ω S - (1 / 4 : ℝ) * ∑ i ∈ P, d i) +
              ∑ i ∈ P, κ i * ((M.f ω S - M.f ω (S.erase i)) - d i)) =
            (1 - ∑ i ∈ P, κ i) * (fμ S - (1 / 4 : ℝ) * ∑ i ∈ P, d i) := by
        simp_rw [mul_add, sum_add_distrib, hterm1, hterm2, add_zero]
      linarith
    have hsum_d_le : ∑ i ∈ P, d i ≤ fμ S := by
      have hP_sub : P ⊆ S := filter_subset _ S
      have hd_nn : ∀ i ∈ S, i ∉ P → 0 ≤ d i := fun i _ _ =>
        sub_nonneg.mpr (hfμ.1 (erase_subset i S))
      have h1 : ∑ i ∈ P, d i ≤ ∑ i ∈ S, d i := sum_le_sum_of_subset_of_nonneg hP_sub hd_nn
      have h2 : ∑ i ∈ S, d i ≤ fμ S - fμ ∅ := sum_teamMarginal_le hsubμ S
      have h3 : 0 ≤ fμ ∅ := (hfμ.2 ∅).1
      linarith
    have h1_κ_pos : 0 ≤ 1 - ∑ i ∈ P, κ i := by linarith
    have h1_α_le_κ : 1 - ∑ i, α i ≤ 1 - ∑ i ∈ P, κ i := by linarith
    have hstep1 :
        (3 / 4 : ℝ) * (1 - ∑ i ∈ P, κ i) * fμ S ≤
          (1 - ∑ i ∈ P, κ i) * (fμ S - (1 / 4 : ℝ) * ∑ i ∈ P, d i) := by
      nlinarith
    have hstep2 :
        (3 / 4 : ℝ) * principalUtility fμ α S ≤
          (3 / 4 : ℝ) * (1 - ∑ i ∈ P, κ i) * fμ S := by
      unfold principalUtility
      nlinarith
    linarith

/-! ### Section 4: Public Signaling Schemes & Universal 3/4 Guarantee -/

/-- Any principal-favorable equilibrium of a stateless contract at the prior induces a
1-point `PUnit` public scheme with the same payoff. -/
lemma principalUtility_mem_publicPayoffs {n m : ℕ} (M : Model n m) (D : Belief m)
    {α : Fin n → ℝ} (hα : IsContract α) {S : Finset (Fin n)}
    (hbest : IsBestEquilibrium (posteriorReward M D) M.c α S) :
    principalUtility (posteriorReward M D) α S ∈ publicPayoffs M D := by
  let π : Measure (Fin m × PUnit) :=
    ∑ ω : Fin m, ENNReal.ofReal (D.1 ω) • Measure.dirac (ω, PUnit.unit)
  have hπ_univ : π Set.univ = 1 := by
    have hsumD : ∑ ω : Fin m, ENNReal.ofReal (D.1 ω) = 1 := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun ω _ => D.2.1 ω), D.2.2, ENNReal.ofReal_one]
    simp only [π, Measure.finsetSum_apply, Measure.smul_apply, Measure.dirac_apply_of_mem
      (Set.mem_univ _), smul_eq_mul, mul_one]
    exact hsumD
  have hπ_prob : IsProbabilityMeasure π := ⟨hπ_univ⟩
  have hπ_rect : ∀ ω₀ : Fin m, π ({ω₀} ×ˢ Set.univ) = ENNReal.ofReal (D.1 ω₀) := by
    intro ω₀
    simp only [π, Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
    rw [sum_eq_single ω₀]
    · rw [Measure.dirac_apply_of_mem (by simp), mul_one]
    · intro ω _ hne
      rw [Measure.dirac_apply' _ ((MeasurableSet.singleton ω₀).prod MeasurableSet.univ),
        Set.indicator_apply, if_neg (by simp [hne]), mul_zero]
    · intro habs
      exact False.elim (habs (mem_univ ω₀))
  have hsig : RiskPersuasion.Convex.IsSignalingScheme (D : Fin m → ℝ) π :=
    ⟨hπ_prob, hπ_rect⟩
  have hbayes : RiskPersuasion.Convex.IsPosterior π (fun _ => (D : Fin m → ℝ)) := by
    refine ⟨fun _ => D.2, fun _ => measurable_const, fun ω₀ B hB => ?_⟩
    by_cases hu : PUnit.unit ∈ B
    · have hB_eq : B = Set.univ := by
        ext x
        cases x
        simp [hu]
      subst hB_eq
      have hmap_prob : IsProbabilityMeasure (π.map Prod.snd) :=
        Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
      rw [hπ_rect ω₀, ENNReal.toReal_ofReal (D.2.1 ω₀), Measure.restrict_univ, integral_const]
      simp only [Measure.real_def, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul]
      rfl
    · have hB_eq : B = ∅ := by
        ext x
        cases x
        simp [hu]
      subst hB_eq
      simp
  have hteam_meas : RiskPersuasion.Convex.IsMeasurableStrategy (fun _ : PUnit => S) := by
    intro T
    by_cases h : S = T <;> simp [h]
  have hint : Integrable (fun p : Fin m × PUnit => principalUtility (M.f p.1) α S) π :=
    Integrable.of_finite
  let A : PublicScheme M D PUnit := {
    joint := π
    signaling := hsig
    posterior := fun _ => D
    bayes := hbayes
    contract := fun _ => α
    contract_bounds := fun _ => hα
    contract_measurable := fun _ => measurable_const
    team := fun _ => S
    team_measurable := hteam_meas
    favorable := Filter.Eventually.of_forall (fun _ => hbest)
    payoff_integrable := hint
  }
  refine ⟨PUnit, inferInstance, inferInstance, inferInstance, inferInstance, A, ?_⟩
  symm
  show ∫ p, principalUtility (M.f p.1) α S ∂π = principalUtility (posteriorReward M D) α S
  rw [integral_fintype hint]
  have hsing : ∀ ω : Fin m, (π {(ω, PUnit.unit)}).toReal = D.1 ω := by
    intro ω
    have hset : ({(ω, PUnit.unit)} : Set (Fin m × PUnit)) = {ω} ×ˢ Set.univ := by
      ext ⟨x, u⟩
      cases u
      simp
    rw [hset, hπ_rect ω, ENNReal.toReal_ofReal (D.2.1 ω)]
  simp only [Measure.real_def, Fintype.sum_prod_type, Fintype.sum_unique, smul_eq_mul, hsing]
  unfold principalUtility posteriorReward
  rw [mul_sum]
  refine sum_congr rfl (fun ω _ => ?_)
  change D.1 ω * ((1 - ∑ i, α i) * M.f ω S) = (1 - ∑ i, α i) * (D.1 ω * M.f ω S)
  ring

lemma publicPayoffs_nonempty {n m : ℕ} (M : Model n m) (D : Belief m) :
    (publicPayoffs M D).Nonempty := by
  let α₀ : Fin n → ℝ := fun _ => 0
  let eqSet : Finset (Finset (Fin n)) :=
    univ.filter (fun T => IsEquilibrium (posteriorReward M D) M.c α₀ T)
  have heq_ne : eqSet.Nonempty := by
    refine ⟨univ.filter (fun i => M.c i = 0), mem_filter.mpr ⟨mem_univ _, ?_⟩⟩
    exact zero_contract_equilibrium (posteriorReward M D) M.c M.cost_nonneg
  obtain ⟨S, hS_mem, hS_max⟩ :=
    exists_max_image eqSet (principalUtility (posteriorReward M D) α₀) heq_ne
  have hbest : IsBestEquilibrium (posteriorReward M D) M.c α₀ S :=
    ⟨(mem_filter.mp hS_mem).2, fun T hT => hS_max T (mem_filter.mpr ⟨mem_univ T, hT⟩)⟩
  exact ⟨_, principalUtility_mem_publicPayoffs M D zero_contract_isContract hbest⟩

lemma publicScheme_value_le_one {n m : ℕ} {M : Model n m} {D : Belief m}
    {Signal : Type} [MeasurableSpace Signal] (A : PublicScheme M D Signal) :
    A.value ≤ 1 := by
  have : IsProbabilityMeasure A.joint := A.signaling.1
  unfold PublicScheme.value
  have hle : ∀ p : Fin m × Signal,
      principalUtility (M.f p.1) (A.contract p.2) (A.team p.2) ≤ 1 :=
    fun p => principalUtility_le_one (M.success p.1) (A.contract_bounds p.2) (A.team p.2)
  have hint1 : Integrable (fun _ : Fin m × Signal => (1 : ℝ)) A.joint := integrable_const 1
  calc
    ∫ p, principalUtility (M.f p.1) (A.contract p.2) (A.team p.2) ∂A.joint ≤
        ∫ _, (1 : ℝ) ∂A.joint :=
      integral_mono A.payoff_integrable hint1 hle
    _ = 1 := by simp [Measure.real_def, measure_univ]

lemma publicPayoffs_bddAbove {n m : ℕ} (M : Model n m) (D : Belief m) :
    BddAbove (publicPayoffs M D) := by
  refine ⟨1, ?_⟩
  rintro u ⟨Signal, _, ms, _, _, A, rfl⟩
  exact @publicScheme_value_le_one n m M D Signal ms A

lemma measurable_eval_team {n : ℕ} {Signal : Type} [MeasurableSpace Signal]
    (g : Finset (Fin n) → ℝ) {team : Signal → Finset (Fin n)}
    (hteam : RiskPersuasion.Convex.IsMeasurableStrategy team) :
    Measurable (fun s => g (team s)) := by
  have heq : (fun s => g (team s)) =
      fun s => ∑ T : Finset (Fin n), (team ⁻¹' {T}).indicator (fun _ => g T) s := by
    ext s
    have hterm : ∀ T : Finset (Fin n),
        (team ⁻¹' {T}).indicator (fun _ => g T) s = if team s = T then g T else 0 := by
      intro T
      by_cases h : team s = T <;> simp [Set.indicator, h]
    simp only [hterm, sum_ite_eq, mem_univ, ↓reduceIte]
  rw [heq]
  exact Finset.measurable_sum univ (fun T _ => measurable_const.indicator (hteam T))

lemma publicScheme_slice_map_eq_withDensity {n m : ℕ} {M : Model n m} {D : Belief m}
    {Signal : Type} [MeasurableSpace Signal] (A : PublicScheme M D Signal) (ω : Fin m) :
    (A.joint.restrict ({ω} ×ˢ Set.univ)).map Prod.snd =
      (A.joint.map Prod.snd).withDensity
        (fun s => ENNReal.ofReal ((A.posterior s : Fin m → ℝ) ω)) := by
  have : IsProbabilityMeasure A.joint := A.signaling.1
  let π_S := A.joint.map Prod.snd
  have : IsProbabilityMeasure π_S :=
    Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  ext B hB
  rw [Measure.map_apply measurable_snd hB, Measure.restrict_apply (measurable_snd hB),
    withDensity_apply _ hB]
  have hset : Prod.snd ⁻¹' B ∩ {ω} ×ˢ (Set.univ : Set Signal) = {ω} ×ˢ B := by
    ext ⟨x, s⟩
    simp [and_comm]
  rw [hset]
  have hfin : A.joint ({ω} ×ˢ B) ≠ ⊤ := measure_ne_top A.joint _
  rw [← ENNReal.ofReal_toReal hfin, A.bayes.2.2 ω B hB]
  have hpost_meas : Measurable (fun s => (A.posterior s : Fin m → ℝ) ω) := A.bayes.2.1 ω
  have hpost_nn : ∀ s, 0 ≤ (A.posterior s : Fin m → ℝ) ω := fun s => (A.bayes.1 s).1 ω
  have hpost_le1 : ∀ s, (A.posterior s : Fin m → ℝ) ω ≤ 1 := by
    intro s
    calc
      (A.posterior s : Fin m → ℝ) ω ≤ ∑ ω' : Fin m, (A.posterior s : Fin m → ℝ) ω' :=
        single_le_sum (fun ω' _ => (A.bayes.1 s).1 ω') (mem_univ ω)
      _ = 1 := (A.bayes.1 s).2
  have hint_B : Integrable (fun s => (A.posterior s : Fin m → ℝ) ω) (π_S.restrict B) := by
    refine Integrable.of_bound hpost_meas.aestronglyMeasurable 1
      (Filter.Eventually.of_forall (fun s => ?_))
    rw [Real.norm_of_nonneg (hpost_nn s)]
    exact hpost_le1 s
  exact ofReal_integral_eq_lintegral_ofReal hint_B (Filter.Eventually.of_forall hpost_nn)

lemma publicScheme_value_eq_posterior_integral {n m : ℕ} {M : Model n m} {D : Belief m}
    {Signal : Type} [MeasurableSpace Signal] (A : PublicScheme M D Signal) :
    A.value =
      ∫ s, principalUtility (posteriorReward M (A.posterior s)) (A.contract s) (A.team s)
        ∂(A.joint.map Prod.snd) := by
  have : IsProbabilityMeasure A.joint := A.signaling.1
  let π_S := A.joint.map Prod.snd
  have : IsProbabilityMeasure π_S :=
    Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  let g : Fin m × Signal → ℝ :=
    fun p => principalUtility (M.f p.1) (A.contract p.2) (A.team p.2)
  let u : Fin m → Signal → ℝ :=
    fun ω s => principalUtility (M.f ω) (A.contract s) (A.team s)
  have hu_meas : ∀ ω : Fin m, Measurable (u ω) := by
    intro ω
    unfold u principalUtility
    exact (measurable_const.sub
      (Finset.measurable_sum univ (fun i _ => A.contract_measurable i))).mul
      (measurable_eval_team (M.f ω) A.team_measurable)
  have hu_bound : ∀ ω s, ‖u ω s‖ ≤ (n : ℝ) + 1 := by
    intro ω s
    dsimp [u, principalUtility]
    have hsum_nn : 0 ≤ ∑ i : Fin n, A.contract s i :=
      sum_nonneg (fun i _ => (A.contract_bounds s i (mem_univ i)).1)
    have hsum_le : ∑ i : Fin n, A.contract s i ≤ n := by
      calc
        ∑ i : Fin n, A.contract s i ≤ ∑ _i : Fin n, (1 : ℝ) :=
          sum_le_sum (fun i _ => (A.contract_bounds s i (mem_univ i)).2)
        _ = n := by simp
    have hf0 : 0 ≤ M.f ω (A.team s) := ((M.success ω).2 (A.team s)).1
    have hf1 : M.f ω (A.team s) ≤ 1 := ((M.success ω).2 (A.team s)).2
    rw [abs_mul, abs_of_nonneg hf0]
    have habs1 : |1 - ∑ i : Fin n, A.contract s i| ≤ (n : ℝ) + 1 := by
      rw [abs_le]
      exact ⟨by linarith, by linarith⟩
    calc
      |1 - ∑ i : Fin n, A.contract s i| * M.f ω (A.team s) ≤
          ((n : ℝ) + 1) * 1 :=
        mul_le_mul habs1 hf1 hf0 (by positivity)
      _ = (n : ℝ) + 1 := mul_one _
  have hpost_bound : ∀ ω s, ‖(A.posterior s : Fin m → ℝ) ω * u ω s‖ ≤ (n : ℝ) + 1 := by
    intro ω s
    have hnn : 0 ≤ (A.posterior s : Fin m → ℝ) ω := (A.bayes.1 s).1 ω
    have hle1 : (A.posterior s : Fin m → ℝ) ω ≤ 1 := by
      calc
        (A.posterior s : Fin m → ℝ) ω ≤ ∑ ω' : Fin m, (A.posterior s : Fin m → ℝ) ω' :=
          single_le_sum (fun ω' _ => (A.bayes.1 s).1 ω') (mem_univ ω)
        _ = 1 := (A.bayes.1 s).2
    rw [norm_mul, Real.norm_of_nonneg hnn]
    calc
      (A.posterior s : Fin m → ℝ) ω * ‖u ω s‖ ≤ 1 * ((n : ℝ) + 1) :=
        mul_le_mul hle1 (hu_bound ω s) (norm_nonneg _) zero_le_one
      _ = (n : ℝ) + 1 := one_mul _
  have hpost_u_int : ∀ ω : Fin m,
      Integrable (fun s => (A.posterior s : Fin m → ℝ) ω * u ω s) π_S := by
    intro ω
    exact Integrable.of_bound
      ((A.bayes.2.1 ω).mul (hu_meas ω)).aestronglyMeasurable ((n : ℝ) + 1)
      (Filter.Eventually.of_forall (hpost_bound ω))
  -- Decompose A.value across states ω : Fin m via indicator functions
  let Sω : Fin m → Set (Fin m × Signal) := fun ω => {ω} ×ˢ Set.univ
  have hSω_meas : ∀ ω : Fin m, MeasurableSet (Sω ω) :=
    fun ω => (MeasurableSet.singleton ω).prod MeasurableSet.univ
  have hval_split : A.value = ∑ ω : Fin m, ∫ p in Sω ω, g p ∂A.joint := by
    unfold PublicScheme.value
    change ∫ p, g p ∂A.joint = _
    have hg_sum : ∀ p : Fin m × Signal, g p = ∑ ω : Fin m, (Sω ω).indicator g p := by
      intro ⟨ω₀, s⟩
      have hterm : ∀ ω : Fin m, (Sω ω).indicator g (ω₀, s) = if ω₀ = ω then g (ω₀, s) else 0 := by
        intro ω
        by_cases h : ω₀ = ω
        · subst h
          unfold Set.indicator
          simp [Sω]
        · unfold Set.indicator
          simp [Sω, h]
      simp only [hterm, sum_ite_eq, mem_univ, ↓reduceIte]
    calc
      ∫ p, g p ∂A.joint = ∫ p, (∑ ω : Fin m, (Sω ω).indicator g p) ∂A.joint :=
        integral_congr_ae (Filter.Eventually.of_forall hg_sum)
      _ = ∑ ω : Fin m, ∫ p, (Sω ω).indicator g p ∂A.joint :=
        integral_finsetSum univ (fun ω _ => A.payoff_integrable.indicator (hSω_meas ω))
      _ = ∑ ω : Fin m, ∫ p in Sω ω, g p ∂A.joint :=
        sum_congr rfl (fun ω _ => integral_indicator (hSω_meas ω))
  have hslice_int : ∀ ω : Fin m,
      ∫ p in Sω ω, g p ∂A.joint =
        ∫ s, (A.posterior s : Fin m → ℝ) ω * u ω s ∂π_S := by
    intro ω
    have hcongr : ∫ p in Sω ω, g p ∂A.joint =
        ∫ p in Sω ω, u ω p.2 ∂A.joint := by
      refine setIntegral_congr_fun (hSω_meas ω) ?_
      intro p hp
      simp only [Sω, Set.mem_prod, Set.mem_singleton_iff, Set.mem_univ, and_true] at hp
      simp [g, u, hp]
    rw [hcongr]
    have hu_aesm : AEStronglyMeasurable (u ω) ((A.joint.restrict (Sω ω)).map Prod.snd) :=
      (hu_meas ω).aestronglyMeasurable
    rw [← integral_map measurable_snd.aemeasurable hu_aesm,
      publicScheme_slice_map_eq_withDensity A ω]
    rw [integral_withDensity_eq_integral_toReal_smul
      (A.bayes.2.1 ω).ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun s => ?_))
    dsimp only
    rw [smul_eq_mul, ENNReal.toReal_ofReal ((A.bayes.1 s).1 ω)]
  rw [hval_split]
  simp_rw [hslice_int]
  rw [← integral_finsetSum univ (fun ω _ => hpost_u_int ω)]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun s => ?_))
  dsimp [u, principalUtility, posteriorReward]
  rw [mul_sum]
  exact sum_congr rfl (fun ω _ => by ring)

lemma three_quarters_optimalInformation_le_fullInformation (n m : ℕ)
    (M : Model n m) (D : Belief m)
    (hsub : ∀ ω, SubsamplingSM.Offline.IsSubmodular (M.f ω)) :
    (3 / 4 : ℝ) * optimalInformation M D ≤ fullInformation M D := by
  have hFI_nonneg : 0 ≤ fullInformation M D :=
    sum_nonneg (fun ω _ => mul_nonneg (D.2.1 ω) (V_nonneg (M.success ω) M.cost_nonneg))
  suffices hmain : ∀ u ∈ publicPayoffs M D, u ≤ (4 / 3 : ℝ) * fullInformation M D by
    have hsup := csSup_le (publicPayoffs_nonempty M D) hmain
    unfold optimalInformation
    linarith
  rintro u ⟨Signal, _, ms, _, _, A, rfl⟩
  let _ : MeasurableSpace Signal := ms
  suffices hval : (3 / 4 : ℝ) * A.value ≤ fullInformation M D by linarith
  have : IsProbabilityMeasure A.joint := A.signaling.1
  let π_S := A.joint.map Prod.snd
  have : IsProbabilityMeasure π_S :=
    Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  rw [publicScheme_value_eq_posterior_integral A]
  let U : Signal → ℝ :=
    fun s => principalUtility (posteriorReward M (A.posterior s)) (A.contract s) (A.team s)
  let F : Signal → ℝ := fun s => fullInformation M (A.posterior s)
  -- Integrability of U and F on π_S
  have hpost_int : ∀ ω : Fin m,
      Integrable (fun s => (A.posterior s : Fin m → ℝ) ω) π_S := by
    intro ω
    refine Integrable.of_bound (A.bayes.2.1 ω).aestronglyMeasurable 1
      (Filter.Eventually.of_forall (fun s => ?_))
    rw [Real.norm_of_nonneg ((A.bayes.1 s).1 ω)]
    calc
      (A.posterior s : Fin m → ℝ) ω ≤ ∑ ω' : Fin m, (A.posterior s : Fin m → ℝ) ω' :=
        single_le_sum (fun ω' _ => (A.bayes.1 s).1 ω') (mem_univ ω)
      _ = 1 := (A.bayes.1 s).2
  have hF_int : Integrable F π_S :=
    integrable_finsetSum univ (fun ω _ => (hpost_int ω).mul_const (V (M.f ω) M.c))
  have hU_meas : Measurable U := by
    have hU_eq : U = fun s => (1 - ∑ i : Fin n, A.contract s i) *
        ∑ ω : Fin m, (A.posterior s : Fin m → ℝ) ω * M.f ω (A.team s) := rfl
    rw [hU_eq]
    exact (measurable_const.sub
      (Finset.measurable_sum univ (fun i _ => A.contract_measurable i))).mul
      (Finset.measurable_sum univ (fun ω _ =>
        (A.bayes.2.1 ω).mul (measurable_eval_team (M.f ω) A.team_measurable)))
  have hU_int : Integrable U π_S := by
    refine Integrable.of_bound hU_meas.aestronglyMeasurable ((n : ℝ) + 1)
      (Filter.Eventually.of_forall (fun s => ?_))
    dsimp [U, principalUtility]
    have hfμ := posteriorReward_isSuccess M (A.posterior s)
    have hf0 : 0 ≤ posteriorReward M (A.posterior s) (A.team s) := (hfμ.2 (A.team s)).1
    have hf1 : posteriorReward M (A.posterior s) (A.team s) ≤ 1 := (hfμ.2 (A.team s)).2
    have hsum_nn : 0 ≤ ∑ i : Fin n, A.contract s i :=
      sum_nonneg (fun i _ => (A.contract_bounds s i (mem_univ i)).1)
    have hsum_le : ∑ i : Fin n, A.contract s i ≤ n := by
      calc
        ∑ i : Fin n, A.contract s i ≤ ∑ _i : Fin n, (1 : ℝ) :=
          sum_le_sum (fun i _ => (A.contract_bounds s i (mem_univ i)).2)
        _ = n := by simp
    rw [abs_mul, abs_of_nonneg hf0]
    have habs1 : |1 - ∑ i : Fin n, A.contract s i| ≤ (n : ℝ) + 1 := by
      rw [abs_le]
      exact ⟨by linarith, by linarith⟩
    calc
      |1 - ∑ i : Fin n, A.contract s i| * posteriorReward M (A.posterior s) (A.team s) ≤
          ((n : ℝ) + 1) * 1 :=
        mul_le_mul habs1 hf1 hf0 (by positivity)
      _ = (n : ℝ) + 1 := mul_one _
  have hae_le : (fun s => (3 / 4 : ℝ) * U s) ≤ᵐ[π_S] F := by
    filter_upwards [A.favorable] with s hs
    have hle_noInfo : U s ≤ noInformation M (A.posterior s) :=
      le_V_of_isEquilibrium (posteriorReward_isSuccess M (A.posterior s))
        (A.contract_bounds s) hs.1
    have h34 := three_quarters_noInformation_le_fullInformation M (A.posterior s) hsub
    dsimp [F]
    linarith
  have hint_le : (3 / 4 : ℝ) * ∫ s, U s ∂π_S ≤ ∫ s, F s ∂π_S := by
    rw [← integral_const_mul]
    exact integral_mono_ae (hU_int.const_mul (3 / 4 : ℝ)) hF_int hae_le
  have hint_F : ∫ s, F s ∂π_S = fullInformation M D := by
    dsimp [F, fullInformation]
    rw [integral_finsetSum univ (fun ω _ => (hpost_int ω).mul_const (V (M.f ω) M.c))]
    refine sum_congr rfl (fun ω _ => ?_)
    rw [integral_mul_const]
    congr 1
    rw [← Measure.restrict_univ (μ := π_S), ← A.bayes.2.2 ω Set.univ MeasurableSet.univ,
      A.signaling.2 ω]
    have hDnn : 0 ≤ (D : Fin m → ℝ) ω := D.2.1 ω
    exact ENNReal.toReal_ofReal hDnn
  linarith

/-! ### Section 5: Additive Sharpness Construction (Proposition 4.3) -/

noncomputable def sharpMval (n : ℕ) : ℝ := 2 * (n : ℝ) ^ 2 + (n : ℝ) + 1
noncomputable def sharpDenom (n : ℕ) : ℝ := (2 * (n : ℝ) - 1) * sharpMval n
noncomputable def sharpCost (n : ℕ) : ℝ := (n : ℝ) / sharpDenom n
noncomputable def sharpWeight (n : ℕ) (ω i : Fin n) : ℝ :=
  if i = ω then (n : ℝ) / (2 * (n : ℝ) - 1) else 1 / (2 * (n : ℝ) - 1)

lemma sharpWeight_pos {n : ℕ} (hn2 : 2 ≤ n) (ω i : Fin n) : 0 < sharpWeight n ω i := by
  have hn_pos : (0 : ℝ) < n := by positivity
  have h2n1 : 0 < 2 * (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    linarith
  by_cases h : i = ω
  · simp only [sharpWeight, h, ↓reduceIte]
    exact div_pos hn_pos h2n1
  · simp only [sharpWeight, h, ↓reduceIte]
    exact div_pos one_pos h2n1

lemma sharpWeight_sum_i {n : ℕ} (hn2 : 2 ≤ n) (ω : Fin n) :
    ∑ i : Fin n, sharpWeight n ω i = 1 := by
  have h2n1 : 0 < 2 * (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    linarith
  rw [← add_sum_erase univ (sharpWeight n ω) (mem_univ ω)]
  have herase : ∑ i ∈ univ.erase ω, sharpWeight n ω i =
      ((n - 1 : ℕ) : ℝ) * (1 / (2 * (n : ℝ) - 1)) := by
    have hcongr : ∑ i ∈ univ.erase ω, sharpWeight n ω i =
        ∑ _i ∈ univ.erase ω, (1 / (2 * (n : ℝ) - 1)) :=
      sum_congr rfl (fun i hi => by rw [sharpWeight, if_neg (ne_of_mem_erase hi)])
    rw [hcongr, sum_const, card_erase_of_mem (mem_univ ω), card_univ, Fintype.card_fin,
      nsmul_eq_mul]
  rw [herase, sharpWeight, if_pos rfl]
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  rw [hcast, mul_one_div, ← add_div]
  have hnum : (n : ℝ) + ((n : ℝ) - 1) = 2 * (n : ℝ) - 1 := by ring
  rw [hnum, div_self (ne_of_gt h2n1)]

lemma sharpWeight_sum_ω {n : ℕ} (hn2 : 2 ≤ n) (i : Fin n) :
    ∑ ω : Fin n, sharpWeight n ω i = 1 := by
  have hsymm : ∑ ω : Fin n, sharpWeight n ω i = ∑ ω : Fin n, sharpWeight n i ω :=
    sum_congr rfl (fun ω _ => by by_cases h : i = ω <;> simp [sharpWeight, h, eq_comm])
  rw [hsymm, sharpWeight_sum_i hn2 i]

noncomputable def sharpModel (n : ℕ) (hn2 : 2 ≤ n) : Model n n where
  f ω S := ∑ i ∈ S, sharpWeight n ω i
  c _ := sharpCost n
  success ω := by
    refine ⟨fun A B hAB => ?_, fun S => ⟨?_, ?_⟩⟩
    · exact sum_le_sum_of_subset_of_nonneg hAB (fun i _ _ => le_of_lt (sharpWeight_pos hn2 ω i))
    · exact sum_nonneg (fun i _ => le_of_lt (sharpWeight_pos hn2 ω i))
    · calc
        ∑ i ∈ S, sharpWeight n ω i ≤ ∑ i : Fin n, sharpWeight n ω i :=
          sum_le_sum_of_subset_of_nonneg (subset_univ S)
            (fun i _ _ => le_of_lt (sharpWeight_pos hn2 ω i))
        _ = 1 := sharpWeight_sum_i hn2 ω
  cost_nonneg _ := by
    have hn_ge2 : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    have h2n1 : 0 < 2 * (n : ℝ) - 1 := by linarith
    have hMval : 0 < sharpMval n := by unfold sharpMval; positivity
    exact le_of_lt (div_pos (by positivity) (mul_pos h2n1 hMval))

noncomputable def sharpBelief (n : ℕ) (hn2 : 2 ≤ n) : Belief n :=
  ⟨fun _ => 1 / (n : ℝ), ⟨fun _ => by positivity, by
    have hn_ne : (n : ℝ) ≠ 0 := by positivity
    rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp⟩⟩

lemma sharp_posteriorReward {n : ℕ} (hn2 : 2 ≤ n) (S : Finset (Fin n)) :
    posteriorReward (sharpModel n hn2) (sharpBelief n hn2) S = (S.card : ℝ) / (n : ℝ) := by
  unfold posteriorReward
  have hcoe : ∀ ω : Fin n, (sharpBelief n hn2 : Fin n → ℝ) ω = 1 / (n : ℝ) := fun _ => rfl
  simp_rw [hcoe]
  change ∑ ω : Fin n, (1 / (n : ℝ)) * (∑ i ∈ S, sharpWeight n ω i) = _
  simp_rw [mul_sum]
  rw [sum_comm]
  have hinner : ∀ i ∈ S, ∑ ω : Fin n, (1 / (n : ℝ)) * sharpWeight n ω i = 1 / (n : ℝ) := by
    intro i _
    rw [← mul_sum, sharpWeight_sum_ω hn2 i, mul_one]
  rw [sum_congr rfl hinner, sum_const, nsmul_eq_mul]
  ring

lemma sharp_optimalInformation_ge {n : ℕ} (hn2 : 2 ≤ n) :
    (3 * (n : ℝ) ^ 3 + (n : ℝ) - 1) / sharpDenom n ≤
      optimalInformation (sharpModel n hn2) (sharpBelief n hn2) := by
  have hn_ge2 : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hn_pos : (0 : ℝ) < n := by positivity
  have h2n1_pos : 0 < 2 * (n : ℝ) - 1 := by linarith
  have hMval_pos : 0 < sharpMval n := by unfold sharpMval; positivity
  have hdenom_pos : 0 < sharpDenom n := mul_pos h2n1_pos hMval_pos
  have hdenom_expand : sharpDenom n = 4 * (n : ℝ) ^ 3 + (n : ℝ) - 1 := by
    unfold sharpDenom sharpMval; ring
  let cval := sharpCost n
  have hcval_pos : 0 < cval := div_pos hn_pos hdenom_pos
  let α₀ : Fin n → ℝ := fun _ => (n : ℝ) * cval
  have hn2c_lt1 : (n : ℝ) ^ 2 * cval < 1 := by
    dsimp [cval, sharpCost]
    rw [show (n : ℝ) ^ 2 * ((n : ℝ) / sharpDenom n) = (n : ℝ) ^ 3 / sharpDenom n by ring]
    rw [div_lt_one hdenom_pos, hdenom_expand]
    nlinarith
  have hα₀_contract : IsContract α₀ := by
    intro i _
    dsimp [α₀]
    refine ⟨by positivity, ?_⟩
    have hn_le_sq : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
    have hle : (n : ℝ) * cval ≤ (n : ℝ) ^ 2 * cval :=
      mul_le_mul_of_nonneg_right hn_le_sq (le_of_lt hcval_pos)
    linarith
  have hα₀_sum : 1 - ∑ i : Fin n, α₀ i = (3 * (n : ℝ) ^ 3 + (n : ℝ) - 1) / sharpDenom n := by
    simp only [α₀, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, cval, sharpCost]
    rw [show (n : ℝ) * ((n : ℝ) * ((n : ℝ) / sharpDenom n)) = (n : ℝ) ^ 3 / sharpDenom n by ring,
      one_sub_div (ne_of_gt hdenom_pos), hdenom_expand]
    congr 1
    ring
  have hα₀_eq : IsEquilibrium (posteriorReward (sharpModel n hn2) (sharpBelief n hn2))
      (sharpModel n hn2).c α₀ univ := by
    rw [isEquilibrium_iff]
    refine ⟨fun i _ => ?_, fun i hi => False.elim (hi (mem_univ i))⟩
    rw [sharp_posteriorReward hn2 univ, sharp_posteriorReward hn2 (univ.erase i),
      card_erase_of_mem (mem_univ i), card_univ, Fintype.card_fin]
    have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
    rw [hcast]
    change cval ≤ (n : ℝ) * cval * ((n : ℝ) / (n : ℝ) - ((n : ℝ) - 1) / (n : ℝ))
    rw [← sub_div, show (n : ℝ) - ((n : ℝ) - 1) = 1 by ring,
      show (n : ℝ) * cval * (1 / (n : ℝ)) = cval * ((n : ℝ) / (n : ℝ)) by ring,
      div_self (ne_of_gt hn_pos), mul_one]
  have hα₀_best : IsBestEquilibrium (posteriorReward (sharpModel n hn2) (sharpBelief n hn2))
      (sharpModel n hn2).c α₀ univ := by
    refine ⟨hα₀_eq, fun T _ => ?_⟩
    unfold principalUtility
    rw [hα₀_sum, sharp_posteriorReward hn2 T, sharp_posteriorReward hn2 univ,
      card_univ, Fintype.card_fin]
    have h1_pos : 0 ≤ (3 * (n : ℝ) ^ 3 + (n : ℝ) - 1) / sharpDenom n :=
      div_nonneg (by nlinarith) (le_of_lt hdenom_pos)
    have hcard_nat : T.card ≤ n := by simpa [Fintype.card_fin] using card_le_univ T
    have hcard_le : (T.card : ℝ) / (n : ℝ) ≤ (n : ℝ) / (n : ℝ) :=
      div_le_div_of_nonneg_right (by exact_mod_cast hcard_nat) (le_of_lt hn_pos)
    exact mul_le_mul_of_nonneg_left hcard_le h1_pos
  have hmem := principalUtility_mem_publicPayoffs (sharpModel n hn2) (sharpBelief n hn2)
    hα₀_contract hα₀_best
  have hpu_univ : principalUtility (posteriorReward (sharpModel n hn2) (sharpBelief n hn2))
      α₀ univ = (3 * (n : ℝ) ^ 3 + (n : ℝ) - 1) / sharpDenom n := by
    unfold principalUtility
    rw [hα₀_sum, sharp_posteriorReward hn2 univ, card_univ, Fintype.card_fin,
      div_self (ne_of_gt hn_pos), mul_one]
  rw [hpu_univ] at hmem
  exact le_csSup (publicPayoffs_bddAbove _ _) hmem

lemma sharp_fullInformation_pos {n : ℕ} (hn2 : 2 ≤ n) :
    0 < fullInformation (sharpModel n hn2) (sharpBelief n hn2) := by
  have hn_ge2 : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hn_pos : (0 : ℝ) < n := by positivity
  have h2n1_pos : 0 < 2 * (n : ℝ) - 1 := by linarith
  have hMval_pos : 0 < sharpMval n := by unfold sharpMval; positivity
  have hxh_pos : 0 < (n : ℝ) / (2 * (n : ℝ) - 1) := div_pos hn_pos h2n1_pos
  have hc_xh : sharpCost n / ((n : ℝ) / (2 * (n : ℝ) - 1)) = 1 / sharpMval n := by
    have h1 : sharpCost n = (1 / sharpMval n) * ((n : ℝ) / (2 * (n : ℝ) - 1)) := by
      unfold sharpCost sharpDenom
      rw [div_mul_div_comm, one_mul, mul_comm]
    rw [h1, mul_div_cancel_right₀ _ (ne_of_gt hxh_pos)]
  have h1M_lt1 : 1 / sharpMval n < 1 := by
    rw [div_lt_one hMval_pos]; unfold sharpMval; nlinarith
  have hV_pos : ∀ ω : Fin n, 0 < V ((sharpModel n hn2).f ω) (sharpModel n hn2).c := by
    intro ω
    let M := sharpModel n hn2
    have hm_pos : ∀ i ∈ ({ω} : Finset (Fin n)),
        0 < M.f ω {ω} - M.f ω (({ω} : Finset (Fin n)).erase i) := by
      intro i hi
      rw [mem_singleton.mp hi]
      simp [M, sharpModel, sharpWeight, hxh_pos]
    have hm_le : ∀ i ∈ ({ω} : Finset (Fin n)),
        M.c i / (M.f ω {ω} - M.f ω (({ω} : Finset (Fin n)).erase i)) ≤ 1 := by
      intro i hi
      rw [mem_singleton.mp hi]
      simp only [M, sharpModel, sum_singleton, erase_singleton, sum_empty, sub_zero,
        sharpWeight, ↓reduceIte]
      rw [hc_xh]
      exact le_of_lt h1M_lt1
    have hle_V := le_V_of_team (M.success ω) M.cost_nonneg {ω} hm_pos hm_le
    have hpos_team :
        0 < (1 - ∑ i ∈ ({ω} : Finset (Fin n)),
              M.c i / (M.f ω {ω} - M.f ω (({ω} : Finset (Fin n)).erase i))) * M.f ω {ω} := by
      simp only [M, sharpModel, sum_singleton, erase_singleton, sum_empty, sub_zero,
        sharpWeight, ↓reduceIte]
      rw [hc_xh]
      exact mul_pos (by linarith) hxh_pos
    exact lt_of_lt_of_le hpos_team hle_V
  have h0 : Fin n := ⟨0, by omega⟩
  have hD_pos : ∀ ω : Fin n, 0 < (sharpBelief n hn2 : Fin n → ℝ) ω :=
    fun _ => div_pos one_pos hn_pos
  exact sum_pos (fun ω _ => mul_pos (hD_pos ω) (hV_pos ω)) ⟨h0, mem_univ h0⟩

lemma sharp_state_V_le {n : ℕ} (hn2 : 2 ≤ n) (ω : Fin n) :
    V ((sharpModel n hn2).f ω) (sharpModel n hn2).c ≤
      (n : ℝ) * (3 * (n : ℝ) + 1) ^ 2 / (4 * sharpDenom n) := by
  let M := sharpModel n hn2
  have hn_ge2 : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hn_pos : (0 : ℝ) < n := by positivity
  have h2n1_pos : 0 < 2 * (n : ℝ) - 1 := by linarith
  have hMval_pos : 0 < sharpMval n := by unfold sharpMval; positivity
  have hdenom_pos : 0 < sharpDenom n := mul_pos h2n1_pos hMval_pos
  have hc_xh : sharpCost n / ((n : ℝ) / (2 * (n : ℝ) - 1)) = 1 / sharpMval n := by
    have h1 : sharpCost n = (1 / sharpMval n) * ((n : ℝ) / (2 * (n : ℝ) - 1)) := by
      unfold sharpCost sharpDenom
      rw [div_mul_div_comm, one_mul, mul_comm]
    rw [h1, mul_div_cancel_right₀ _ (ne_of_gt (div_pos hn_pos h2n1_pos))]
  have hc_xl : sharpCost n / (1 / (2 * (n : ℝ) - 1)) = (n : ℝ) / sharpMval n := by
    have h1 : sharpCost n = ((n : ℝ) / sharpMval n) * (1 / (2 * (n : ℝ) - 1)) := by
      unfold sharpCost sharpDenom
      rw [div_mul_div_comm, mul_one, mul_comm]
    rw [h1, mul_div_cancel_right₀ _ (ne_of_gt (div_pos one_pos h2n1_pos))]
  refine csSup_le (statelessPayoffs_nonempty (M.f ω) M.c M.cost_nonneg) ?_
  rintro u ⟨α, S, hα, heq, rfl⟩
  rw [isEquilibrium_iff] at heq
  have hα_lb : ∀ i ∈ S, sharpCost n / sharpWeight n ω i ≤ α i := by
    intro i hi
    have hmarg : M.f ω S - M.f ω (S.erase i) = sharpWeight n ω i := by
      change (∑ j ∈ S, sharpWeight n ω j) - (∑ j ∈ S.erase i, sharpWeight n ω j) = _
      have := sum_erase_add S (sharpWeight n ω) hi
      linarith
    have hic := heq.1 i hi
    rw [hmarg] at hic
    exact (div_le_iff₀ (sharpWeight_pos hn2 ω i)).mpr hic
  have hsum_α_ge : ∑ i ∈ S, sharpCost n / sharpWeight n ω i ≤ ∑ i : Fin n, α i := by
    calc
      ∑ i ∈ S, sharpCost n / sharpWeight n ω i ≤ ∑ i ∈ S, α i := sum_le_sum hα_lb
      _ ≤ ∑ i : Fin n, α i := sum_le_univ_sum_of_nonneg (fun i => (hα i (mem_univ i)).1)
  have hfS_nn : 0 ≤ M.f ω S := ((M.success ω).2 S).1
  have hpu_le : principalUtility (M.f ω) α S ≤
      (1 - ∑ i ∈ S, sharpCost n / sharpWeight n ω i) * M.f ω S := by
    unfold principalUtility
    exact mul_le_mul_of_nonneg_right (by linarith) hfS_nn
  by_cases hωS : ω ∈ S
  · let s : ℝ := ((S.erase ω).card : ℝ)
    have hsum_min : ∑ i ∈ S, sharpCost n / sharpWeight n ω i =
        (1 + (n : ℝ) * s) / sharpMval n := by
      rw [← add_sum_erase S (fun i => sharpCost n / sharpWeight n ω i) hωS]
      have herase : ∑ i ∈ S.erase ω, sharpCost n / sharpWeight n ω i =
          s * ((n : ℝ) / sharpMval n) := by
        have hcongr : ∑ i ∈ S.erase ω, sharpCost n / sharpWeight n ω i =
            ∑ _i ∈ S.erase ω, (n : ℝ) / sharpMval n :=
          sum_congr rfl (fun i hi => by rw [sharpWeight, if_neg (ne_of_mem_erase hi), hc_xl])
        rw [hcongr, sum_const, nsmul_eq_mul]
      rw [sharpWeight, if_pos rfl, hc_xh, herase, mul_div_assoc', ← add_div]
      congr 1
      ring
    have hfS_eq : M.f ω S = ((n : ℝ) + s) / (2 * (n : ℝ) - 1) := by
      change ∑ i ∈ S, sharpWeight n ω i = _
      rw [← add_sum_erase S (sharpWeight n ω) hωS]
      have herase : ∑ i ∈ S.erase ω, sharpWeight n ω i = s * (1 / (2 * (n : ℝ) - 1)) := by
        have hcongr : ∑ i ∈ S.erase ω, sharpWeight n ω i =
            ∑ _i ∈ S.erase ω, (1 / (2 * (n : ℝ) - 1)) :=
          sum_congr rfl (fun i hi => by rw [sharpWeight, if_neg (ne_of_mem_erase hi)])
        rw [hcongr, sum_const, nsmul_eq_mul]
      rw [sharpWeight, if_pos rfl, herase, mul_one_div, ← add_div]
    have hprod_eq :
        (1 - ∑ i ∈ S, sharpCost n / sharpWeight n ω i) * M.f ω S =
          (n : ℝ) * (2 * (n : ℝ) + 1 - s) * ((n : ℝ) + s) / sharpDenom n := by
      rw [hsum_min, hfS_eq, one_sub_div (ne_of_gt hMval_pos), div_mul_div_comm]
      unfold sharpDenom sharpMval
      rw [mul_comm (2 * (n : ℝ) ^ 2 + (n : ℝ) + 1) (2 * (n : ℝ) - 1)]
      congr 1
      ring
    have hquad : 4 * (2 * (n : ℝ) + 1 - s) * ((n : ℝ) + s) ≤ (3 * (n : ℝ) + 1) ^ 2 := by
      have hsq : 0 ≤ (2 * s - (n : ℝ) - 1) ^ 2 := sq_nonneg _
      linarith
    have hnum_le :
        4 * ((n : ℝ) * (2 * (n : ℝ) + 1 - s) * ((n : ℝ) + s)) ≤
          (n : ℝ) * (3 * (n : ℝ) + 1) ^ 2 := by
      nlinarith
    have hbound :
        (n : ℝ) * (2 * (n : ℝ) + 1 - s) * ((n : ℝ) + s) / sharpDenom n ≤
          (n : ℝ) * (3 * (n : ℝ) + 1) ^ 2 / (4 * sharpDenom n) := by
      rw [div_le_div_iff₀ hdenom_pos (by positivity)]
      nlinarith
    linarith
  · let s : ℝ := (S.card : ℝ)
    have hs_nn : 0 ≤ s := Nat.cast_nonneg _
    have hs_nat : S.card ≤ n := by simpa [Fintype.card_fin] using card_le_univ S
    have hs_le_n : s ≤ (n : ℝ) := by dsimp [s]; exact_mod_cast hs_nat
    have hsum_min : ∑ i ∈ S, sharpCost n / sharpWeight n ω i =
        (s * (n : ℝ)) / sharpMval n := by
      have hcongr : ∑ i ∈ S, sharpCost n / sharpWeight n ω i =
          ∑ _i ∈ S, (n : ℝ) / sharpMval n :=
        sum_congr rfl (fun i hi => by
          have hne : i ≠ ω := fun heq => hωS (heq ▸ hi)
          rw [sharpWeight, if_neg hne, hc_xl])
      rw [hcongr, sum_const, nsmul_eq_mul, mul_div_assoc']
    have hfS_eq : M.f ω S = s / (2 * (n : ℝ) - 1) := by
      change ∑ i ∈ S, sharpWeight n ω i = _
      have hcongr : ∑ i ∈ S, sharpWeight n ω i = ∑ _i ∈ S, (1 / (2 * (n : ℝ) - 1)) :=
        sum_congr rfl (fun i hi => by
          have hne : i ≠ ω := fun heq => hωS (heq ▸ hi)
          rw [sharpWeight, if_neg hne])
      rw [hcongr, sum_const, nsmul_eq_mul, mul_one_div]
    have hprod_eq :
        (1 - ∑ i ∈ S, sharpCost n / sharpWeight n ω i) * M.f ω S =
          s * (sharpMval n - (n : ℝ) * s) / sharpDenom n := by
      rw [hsum_min, hfS_eq, one_sub_div (ne_of_gt hMval_pos), div_mul_div_comm]
      unfold sharpDenom
      rw [mul_comm (sharpMval n) (2 * (n : ℝ) - 1)]
      congr 1
      ring
    have hquad1 : s * (sharpMval n - (n : ℝ) * s) ≤
        (n : ℝ) * ((n : ℝ) ^ 2 + (n : ℝ) + 1) := by
      have hid : (n : ℝ) * ((n : ℝ) ^ 2 + (n : ℝ) + 1) - s * (sharpMval n - (n : ℝ) * s) =
          ((n : ℝ) - s) * ((n : ℝ) * ((n : ℝ) - s) + (n : ℝ) + 1) := by
        unfold sharpMval; ring
      have h1 : 0 ≤ (n : ℝ) - s := by linarith
      have h2 : 0 ≤ (n : ℝ) * ((n : ℝ) - s) + (n : ℝ) + 1 := by nlinarith
      have hprod_nn : 0 ≤ ((n : ℝ) - s) * ((n : ℝ) * ((n : ℝ) - s) + (n : ℝ) + 1) :=
        mul_nonneg h1 h2
      linarith
    have hquad2 : 4 * ((n : ℝ) * ((n : ℝ) ^ 2 + (n : ℝ) + 1)) ≤
        (n : ℝ) * (3 * (n : ℝ) + 1) ^ 2 := by
      have hid : (n : ℝ) * (3 * (n : ℝ) + 1) ^ 2 -
          4 * ((n : ℝ) * ((n : ℝ) ^ 2 + (n : ℝ) + 1)) =
          5 * (n : ℝ) ^ 3 + 2 * (n : ℝ) ^ 2 - 3 * (n : ℝ) := by ring
      nlinarith
    have hbound :
        s * (sharpMval n - (n : ℝ) * s) / sharpDenom n ≤
          (n : ℝ) * (3 * (n : ℝ) + 1) ^ 2 / (4 * sharpDenom n) := by
      rw [div_le_div_iff₀ hdenom_pos (by positivity)]
      nlinarith
    linarith

lemma additive_sharpness (β : ℝ) (hβ1 : 1 ≤ β) (hβ43 : β < (4 / 3 : ℝ)) :
    ∃ (n m : ℕ) (M : Model n m) (D : Belief m),
      (∀ ω, FairTeamContracts.IsAdditive (M.f ω)) ∧
      0 < fullInformation M D ∧ β * fullInformation M D < optimalInformation M D := by
  let ε : ℝ := (4 / 3 : ℝ) - β
  have hε_pos : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨k, hk⟩ := exists_nat_gt (1 / ε)
  let n : ℕ := k + 2
  have hn2 : 2 ≤ n := by omega
  have hn_pos_real : (0 : ℝ) < n := by positivity
  have hn_ge2_real : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hk_lt_n : (k : ℝ) < n := by exact_mod_cast (by omega : k < n)
  have hεn_gt1 : 1 < ε * (n : ℝ) := by
    have h1 : 1 / ε < (n : ℝ) := lt_trans hk hk_lt_n
    have := (div_lt_iff₀ hε_pos).mp h1
    linarith
  have h2n1_pos : 0 < 2 * (n : ℝ) - 1 := by linarith
  have hMval_pos : 0 < sharpMval n := by unfold sharpMval; positivity
  have hdenom_pos : 0 < sharpDenom n := mul_pos h2n1_pos hMval_pos
  let M := sharpModel n hn2
  let D := sharpBelief n hn2
  have hf_add : ∀ ω : Fin n, FairTeamContracts.IsAdditive (M.f ω) := by
    intro ω S
    simp [M, sharpModel]
  have hFI_pos : 0 < fullInformation M D := sharp_fullInformation_pos hn2
  let Ubound : ℝ := (n : ℝ) * (3 * (n : ℝ) + 1) ^ 2 / (4 * sharpDenom n)
  have hFI_le : fullInformation M D ≤ Ubound := by
    have hcoe : ∀ ω : Fin n, (D : Fin n → ℝ) ω = 1 / (n : ℝ) := fun _ => rfl
    calc
      fullInformation M D = ∑ ω : Fin n, (1 / (n : ℝ)) * V (M.f ω) M.c := by
        unfold fullInformation
        exact sum_congr rfl (fun ω _ => by rw [hcoe ω])
      _ ≤ ∑ _ω : Fin n, (1 / (n : ℝ)) * Ubound :=
        sum_le_sum (fun ω _ =>
          mul_le_mul_of_nonneg_left (sharp_state_V_le hn2 ω) (by positivity))
      _ = Ubound := by
        rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp
  have hβ_Ubound_lt : β * Ubound < (3 * (n : ℝ) ^ 3 + (n : ℝ) - 1) / sharpDenom n := by
    have hβ_eq : β = (4 / 3 : ℝ) - ε := by dsimp [ε]; ring
    have hnum_lt : β * ((n : ℝ) * (3 * (n : ℝ) + 1) ^ 2) <
        4 * (3 * (n : ℝ) ^ 3 + (n : ℝ) - 1) := by
      have hid :
          4 * (3 * (n : ℝ) ^ 3 + (n : ℝ) - 1) -
              ((4 / 3 : ℝ) - ε) * ((n : ℝ) * (3 * (n : ℝ) + 1) ^ 2) =
            (n : ℝ) ^ 2 * (9 * (ε * (n : ℝ)) - 8) + 6 * ε * (n : ℝ) ^ 2 +
              ε * (n : ℝ) + ((8 / 3 : ℝ) * (n : ℝ) - 4) := by
        ring
      rw [hβ_eq]
      have h1 : 0 < (n : ℝ) ^ 2 * (9 * (ε * (n : ℝ)) - 8) :=
        mul_pos (by positivity) (by linarith)
      have h2 : 0 < 6 * ε * (n : ℝ) ^ 2 := by positivity
      have h3 : 0 < ε * (n : ℝ) := by linarith
      have h4 : 0 < (8 / 3 : ℝ) * (n : ℝ) - 4 := by linarith
      linarith
    dsimp [Ubound]
    rw [show β * ((n : ℝ) * (3 * (n : ℝ) + 1) ^ 2 / (4 * sharpDenom n)) =
          (β * ((n : ℝ) * (3 * (n : ℝ) + 1) ^ 2)) / (4 * sharpDenom n) by ring]
    rw [div_lt_div_iff₀ (by positivity) hdenom_pos]
    nlinarith
  have hopt_ge := sharp_optimalInformation_ge hn2
  have hβ_FI_lt : β * fullInformation M D < optimalInformation M D := by
    have h1 : β * fullInformation M D ≤ β * Ubound :=
      mul_le_mul_of_nonneg_left hFI_le (by linarith)
    linarith
  exact ⟨n, n, M, D, hf_add, hFI_pos, hβ_FI_lt⟩

end TransparencyTeamContracts_Submodular_Proof

open TransparencyTeamContracts.Submodular

theorem solution :
    (∀ (n m : ℕ) (M : Model n m) (D : Belief m),
      (∀ ω, SubsamplingSM.Offline.IsSubmodular (M.f ω)) →
        (3 / 4 : ℝ) * optimalInformation M D ≤ fullInformation M D) ∧
    (∀ β : ℝ, 1 ≤ β → β < (4 / 3 : ℝ) →
      ∃ (n m : ℕ) (M : Model n m) (D : Belief m),
        (∀ ω, FairTeamContracts.IsAdditive (M.f ω)) ∧
        0 < fullInformation M D ∧ β * fullInformation M D < optimalInformation M D) :=
  ⟨TransparencyTeamContracts_Submodular_Proof.three_quarters_optimalInformation_le_fullInformation,
   TransparencyTeamContracts_Submodular_Proof.additive_sharpness⟩
