-- Prove2me | solution 1 for RandOnlineSetCoverSqrt.LowerBound.Supplement.theorem_1_4
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T19:27:27.015858+00:00
-- url     : https://prove2.me/submissions/c19f96e7-63a5-442b-9faa-7d02bf3bdbe5

import Mathlib
import Definitions.Def_RandOnlineSetCoverSqrt_LowerBound_Halving
import Theorems.Thm_RandOnlineSetCoverSqrt_LowerBound_lemma_3_1
import Definitions.Def_RandOnlineSetCoverSqrt_LowerBound_Supplement_RandomOrder
import Theorems.Thm_RandOnlineSetCoverSqrt_LowerBound_lemma_3_5
import Theorems.Thm_RandOnlineSetCoverSqrt_LowerBound_lemma_4_1

section
set_option autoImplicit false

open scoped ENNReal

namespace RandOnlineSetCoverSqrt.Dev.T14A
open RandOnlineSetCoverSqrt.LowerBound RandOnlineSetCover.InfoLB

/-! ### Section 1: batches, the probability space, the chain of families -/

section Chain

variable {m : ℕ}

/-- The forcing batch of `D` supplied by Lemma 3.1 (empty in degenerate cases). -/
noncomputable def batch (r : ℕ) (D : Family m) : List (Element m) :=
  if h : D.Nonempty ∧ (∀ W ∈ D, W.Nonempty) ∧ 1 ≤ r then
    (lemma_3_1 D h.1 h.2.1 r h.2.2).choose
  else []

theorem batch_forcing (r : ℕ) (D : Family m) (hD : D.Nonempty) (hne : ∀ W ∈ D, W.Nonempty)
    (hr : 1 ≤ r) : Forcing r D (batch r D) := by
  have h : D.Nonempty ∧ (∀ W ∈ D, W.Nonempty) ∧ 1 ≤ r := ⟨hD, hne, hr⟩
  unfold batch
  rw [dif_pos h]
  exact (lemma_3_1 D h.1 h.2.1 r h.2.2).choose_spec.1

/-- An enumeration of the halves of a family. -/
noncomputable def halvesList (E : Family m) : List (Family m) :=
  (E.powersetCard (E.card / 2)).toList

theorem halvesList_length (E : Family m) :
    (halvesList E).length = Nat.choose E.card (E.card / 2) := by
  simp [halvesList, Finset.length_toList, Finset.card_powersetCard]

theorem mem_halvesList {E D : Family m} :
    D ∈ halvesList E ↔ D ⊆ E ∧ D.card = E.card / 2 := by
  simp [halvesList, Finset.mem_powersetCard]

theorem halvesList_nodup (E : Family m) : (halvesList E).Nodup :=
  Finset.nodup_toList _

/-- Number of halves of a family of size `2^(T-s)`. -/
def Nn (T s : ℕ) : ℕ := Nat.choose (2 ^ (T - s)) (2 ^ (T - s) / 2)

theorem Nn_pos (T s : ℕ) : 0 < Nn T s := Nat.choose_pos (Nat.div_le_self _ _)

/-- The probability space: an index of a half at each step. -/
abbrev Omega (T : ℕ) := (t : Fin T) → Fin (Nn T t.val)

instance omegaNonempty (T : ℕ) : Nonempty (Omega T) :=
  ⟨fun t => ⟨0, Nn_pos T t.val⟩⟩

/-- The chain of families `C^0 = C₀, C^{t+1} = ` the `ω t`-th half of `C^t`. -/
noncomputable def cN (C₀ : Family m) {T : ℕ} (ω : Omega T) : ℕ → Family m
  | 0 => C₀
  | s + 1 => if h : s < T then (halvesList (cN C₀ ω s)).getD (ω ⟨s, h⟩).val ∅
      else cN C₀ ω s

theorem cN_succ (C₀ : Family m) {T : ℕ} (ω : Omega T) (t : Fin T) :
    cN C₀ ω (t.val + 1) = (halvesList (cN C₀ ω t.val)).getD (ω t).val ∅ := by
  simp [cN, t.isLt]

/-- `cN ω s` only depends on the coordinates `< s`. -/
theorem cN_congr (C₀ : Family m) {T : ℕ} (ω ω' : Omega T) (s : ℕ)
    (h : ∀ u : Fin T, u.val < s → ω u = ω' u) : cN C₀ ω s = cN C₀ ω' s := by
  induction s with
  | zero => rfl
  | succ s ih =>
    have ih' := ih (fun u hu => h u (by omega))
    simp only [cN]
    split_ifs with hs
    · rw [ih', h ⟨s, hs⟩ (by simp)]
    · exact ih'

theorem two_pow_half (T s : ℕ) (hs : s < T) : 2 ^ (T - s) / 2 = 2 ^ (T - (s + 1)) := by
  have : T - s = (T - (s + 1)) + 1 := by omega
  rw [this, pow_succ, Nat.mul_div_cancel _ (by norm_num)]

/-- Invariant of the chain: sizes `2^(T-s)`, inside `C₀`, and each step is a half. -/
theorem cN_card (C₀ : Family m) {T : ℕ} (hC : C₀.card = 2 ^ T) (ω : Omega T) :
    ∀ s, s ≤ T → (cN C₀ ω s).card = 2 ^ (T - s) ∧ cN C₀ ω s ⊆ C₀ := by
  intro s
  induction s with
  | zero => intro _; simp [cN, hC]
  | succ s ih =>
    intro hs
    obtain ⟨h1, h2⟩ := ih (by omega)
    have hlt : s < T := by omega
    have hmem := cN_succ C₀ ω ⟨s, hlt⟩
    simp only at hmem
    have hidx : (ω ⟨s, hlt⟩).val < (halvesList (cN C₀ ω s)).length := by
      rw [halvesList_length, h1]; exact (ω ⟨s, hlt⟩).isLt
    rw [List.getD_eq_getElem _ _ hidx] at hmem
    have hm2 := List.getElem_mem hidx
    rw [← hmem, mem_halvesList] at hm2
    refine ⟨?_, hm2.1.trans h2⟩
    rw [hm2.2, h1, two_pow_half T s hlt]

theorem cN_succ_mem (C₀ : Family m) {T : ℕ} (hC : C₀.card = 2 ^ T) (ω : Omega T) (t : Fin T) :
    cN C₀ ω (t.val + 1) ∈ halvesList (cN C₀ ω t.val) ∧
      cN C₀ ω (t.val + 1) = (halvesList (cN C₀ ω t.val))[(ω t).val]'(by
        rw [halvesList_length, (cN_card C₀ hC ω t.val t.isLt.le).1]; exact (ω t).isLt) := by
  have hidx : (ω t).val < (halvesList (cN C₀ ω t.val)).length := by
    rw [halvesList_length, (cN_card C₀ hC ω t.val t.isLt.le).1]; exact (ω t).isLt
  rw [cN_succ, List.getD_eq_getElem _ _ hidx]
  exact ⟨List.getElem_mem _, rfl⟩

theorem cN_antitone (C₀ : Family m) {T : ℕ} (hC : C₀.card = 2 ^ T) (ω : Omega T) :
    ∀ s s', s ≤ s' → s' ≤ T → cN C₀ ω s' ⊆ cN C₀ ω s := by
  intro s s' hss' hs'
  induction s' with
  | zero => simp [Nat.le_zero.mp hss']
  | succ s' ih =>
    rcases Nat.of_le_succ hss' with h | h
    · have := (mem_halvesList.mp (cN_succ_mem C₀ hC ω ⟨s', by omega⟩).1).1
      exact this.trans (ih h (by omega))
    · rw [h]

end Chain

section Mono
variable {m : ℕ}
/-- `chosen` is monotone along prefixes. -/
theorem chosen_mono {n : ℕ} (A : Rule m n) {σ σ' : List (Finset (Fin m))} (h : σ <+: σ') :
    chosen A σ ⊆ chosen A σ' := by
  intro x hx
  simp only [chosen, Finset.mem_biUnion, Finset.mem_univ, true_and] at hx ⊢
  obtain ⟨t, ht⟩ := hx
  refine ⟨t, ?_⟩
  split_ifs at ht with h1
  · have h2 : t.val < σ'.length := lt_of_lt_of_le h1 h.length_le
    rw [if_pos h2]
    have : (fun i : Fin (t.val + 1) => σ[i.val]?.getD ∅) =
        (fun i : Fin (t.val + 1) => σ'[i.val]?.getD ∅) := by
      funext i
      have hi : i.val < σ.length := lt_of_le_of_lt (Nat.lt_succ_iff.mp i.isLt) h1
      rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem (lt_of_lt_of_le hi h.length_le),
        h.getElem hi]
    rw [← this]; exact ht
  · simp at ht
end Mono


/-! ### The trajectory law of a chain with an adapted purchase process -/

section Law

variable {m : ℕ}

/-- The trajectory `(C^t, X_t)_{t ≤ T}` for a coin vector `ω`. -/
noncomputable def trajX (C₀ : Family m) {T : ℕ} (X : Omega T → ℕ → Finset (Fin m)) (ω : Omega T) :
    Trajectory m T :=
  (fun s => cN C₀ ω s.val, fun s => X ω s.val)

/-- The law of the trajectory. -/
noncomputable def pAX (C₀ : Family m) (T : ℕ) (X : Omega T → ℕ → Finset (Fin m)) :
    PMF (Trajectory m T) :=
  (PMF.uniformOfFintype (Omega T)).map (trajX C₀ X)

theorem mem_support_pAX (C₀ : Family m) (T : ℕ) (X : Omega T → ℕ → Finset (Fin m))
    (z : Trajectory m T) (hz : pAX C₀ T X z ≠ 0) : ∃ ω : Omega T, trajX C₀ X ω = z := by
  obtain ⟨ω, _, h⟩ := (PMF.mem_support_map_iff _ _ _).mp ((PMF.mem_support_iff _ _).mpr hz)
  exact ⟨ω, h⟩

open Classical in
theorem eventMass_map {α : Type*} [Fintype α] [Nonempty α] {T : ℕ} (f : α → Trajectory m T)
    (E : Trajectory m T → Prop) :
    eventMass ((PMF.uniformOfFintype α).map f) E =
      ((Finset.univ.filter (fun a => E (f a))).card : ℝ≥0∞) / Fintype.card α := by
  unfold eventMass
  simp only [PMF.map_apply, tsum_fintype, PMF.uniformOfFintype_apply]
  set c : ℝ≥0∞ := (Fintype.card α : ℝ≥0∞)⁻¹
  have key : ∀ z, (if E z then ∑ a, (if z = f a then c else 0) else 0) =
      ∑ a, if z = f a then (if E (f a) then c else 0) else 0 := by
    intro z
    split_ifs with h
    · refine Finset.sum_congr rfl fun a _ => ?_
      by_cases hz : z = f a
      · subst hz; simp [h]
      · simp [hz]
    · symm; refine Finset.sum_eq_zero fun a _ => ?_
      by_cases hz : z = f a
      · subst hz; simp [h]
      · simp [hz]
  rw [Finset.sum_congr rfl (fun z _ => key z), Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
    div_eq_mul_inv]

theorem terminal_map {α : Type*} [Fintype α] [Nonempty α] {T : ℕ} (f : α → Trajectory m T) :
    terminalExpectation ((PMF.uniformOfFintype α).map f) =
      ∑ a, (Fintype.card α : ℝ)⁻¹ * (((f a).2 (Fin.last T)).card : ℝ) := by
  unfold terminalExpectation
  simp only [PMF.map_apply, tsum_fintype, PMF.uniformOfFintype_apply]
  set c : ℝ≥0∞ := (Fintype.card α : ℝ≥0∞)⁻¹
  have hc : c.toReal = (Fintype.card α : ℝ)⁻¹ := by simp [c]
  have hct : c ≠ ⊤ := by simp [c]
  have key : ∀ z, (∑ a, (if z = f a then c else 0)).toReal * ((z.2 (Fin.last T)).card : ℝ) =
      ∑ a, if z = f a then c.toReal * (((f a).2 (Fin.last T)).card : ℝ) else 0 := by
    intro z
    rw [ENNReal.toReal_sum (fun a _ => by split_ifs <;> simp [hct]), Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases hz : z = f a
    · subst hz; simp
    · simp [hz]
  rw [Finset.sum_congr rfl (fun z _ => key z), Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, hc]

/-- Equal slices: a predicate not reading coordinate `t` is split evenly by `ω t`. -/
theorem slice_card {T : ℕ} (P : Omega T → Prop) [DecidablePred P] (t : Fin T)
    (hP : ∀ ω (j : Fin (Nn T t.val)), P (Function.update ω t j) ↔ P ω) (j : Fin (Nn T t.val)) :
    (Finset.univ.filter (fun ω => P ω ∧ ω t = j)).card * Nn T t.val =
      (Finset.univ.filter P).card := by
  have hsame : ∀ j' : Fin (Nn T t.val), (Finset.univ.filter (fun ω => P ω ∧ ω t = j')).card =
      (Finset.univ.filter (fun ω => P ω ∧ ω t = j)).card := by
    intro j'
    apply Finset.card_nbij' (fun ω => Function.update ω t j) (fun ω => Function.update ω t j')
    · intro ω hω
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hω ⊢
      exact ⟨(hP ω j).mpr hω.1, by simp⟩
    · intro ω hω
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hω ⊢
      exact ⟨(hP ω j').mpr hω.1, by simp⟩
    · intro ω hω
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hω
      simp only [Function.update_idem]
      rw [← hω.2, Function.update_eq_self]
    · intro ω hω
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hω
      simp only [Function.update_idem]
      rw [← hω.2, Function.update_eq_self]
  rw [Finset.card_eq_sum_card_fiberwise (s := Finset.univ.filter P) (f := fun ω => ω t)
    (t := Finset.univ)
    (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _))]
  simp only [Finset.filter_filter]
  rw [Finset.sum_congr rfl (fun b _ => hsame b), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, mul_comm]

theorem trajX_update (C₀ : Family m) {T : ℕ} (X : Omega T → ℕ → Finset (Fin m))
    (hX : ∀ ω (t : Fin T) (j : Fin (Nn T t.val)) (s : ℕ), s ≤ t.val →
      X (Function.update ω t j) s = X ω s) (ω : Omega T)
    (t : Fin T) (j : Fin (Nn T t.val)) (s : ℕ) (hs : s ≤ t.val) :
    cN C₀ (Function.update ω t j) s = cN C₀ ω s ∧
      X (Function.update ω t j) s = X ω s := by
  refine ⟨?_, hX ω t j s hs⟩
  apply cN_congr
  intro v hv
  have : v ≠ t := by intro h; subst h; omega
  simp [Function.update_of_ne this]

theorem halving_eq (C₀ : Family m) {T : ℕ} (X : Omega T → ℕ → Finset (Fin m))
    (hX : ∀ ω (t : Fin T) (j : Fin (Nn T t.val)) (s : ℕ), s ≤ t.val →
      X (Function.update ω t j) s = X ω s)
    (hC : C₀.card = 2 ^ T) (t : Fin T) (h : Trajectory m T) (D : Family m) :
    eventMass (pAX C₀ T X) (fun z => sameHistory t z h ∧ z.1 t.succ = D) =
      if D ⊆ h.1 t.castSucc ∧ D.card = (h.1 t.castSucc).card / 2 then
        eventMass (pAX C₀ T X) (fun z => sameHistory t z h) /
          (Nat.choose (h.1 t.castSucc).card ((h.1 t.castSucc).card / 2) : ℝ≥0∞)
      else 0 := by
  classical
  unfold pAX
  rw [eventMass_map, eventMass_map]
  have hP : ∀ ω (j : Fin (Nn T t.val)), sameHistory t (trajX C₀ X (Function.update ω t j)) h ↔
      sameHistory t (trajX C₀ X ω) h := by
    intro ω j
    simp only [sameHistory, trajX]
    constructor
    · intro H s hs
      obtain ⟨h1, h2⟩ := trajX_update C₀ X hX ω t j s.val hs
      rw [← h1, ← h2]; exact H s hs
    · intro H s hs
      obtain ⟨h1, h2⟩ := trajX_update C₀ X hX ω t j s.val hs
      rw [h1, h2]; exact H s hs
  have hsucc : ∀ ω : Omega T, (trajX C₀ X ω).1 t.succ = cN C₀ ω (t.val + 1) := fun ω => rfl
  suffices main : ((Finset.univ.filter (fun ω => sameHistory t (trajX C₀ X ω) h ∧
      (trajX C₀ X ω).1 t.succ = D)).card : ℝ≥0∞) / Fintype.card (Omega T) =
      if D ⊆ h.1 t.castSucc ∧ D.card = (h.1 t.castSucc).card / 2 then
        ((Finset.univ.filter (fun ω => sameHistory t (trajX C₀ X ω) h)).card : ℝ≥0∞) /
          Fintype.card (Omega T) /
          (Nat.choose (h.1 t.castSucc).card ((h.1 t.castSucc).card / 2) : ℝ≥0∞)
      else 0 by convert main
  by_cases hne : ∃ ω₀, sameHistory t (trajX C₀ X ω₀) h
  · obtain ⟨ω₀, h₀⟩ := hne
    have hcE : ∀ ω, sameHistory t (trajX C₀ X ω) h → cN C₀ ω t.val = h.1 t.castSucc :=
      fun ω hω => (hω t.castSucc (by simp)).1
    have hcard : (h.1 t.castSucc).card = 2 ^ (T - t.val) := by
      rw [← hcE ω₀ h₀]; exact (cN_card C₀ hC ω₀ t.val t.isLt.le).1
    have hlen : (halvesList (h.1 t.castSucc)).length = Nn T t.val := by
      rw [halvesList_length, hcard]; rfl
    have hval : ∀ ω, sameHistory t (trajX C₀ X ω) h → cN C₀ ω (t.val + 1) =
        (halvesList (h.1 t.castSucc))[(ω t).val]'(by rw [hlen]; exact (ω t).isLt) := by
      intro ω hω
      rw [cN_succ, hcE ω hω, List.getD_eq_getElem]
    split_ifs with hD
    · have hDmem : D ∈ halvesList (h.1 t.castSucc) := mem_halvesList.mpr hD
      obtain ⟨j, hj, hjD⟩ := List.mem_iff_getElem.mp hDmem
      let jj : Fin (Nn T t.val) := ⟨j, by rw [← hlen]; exact hj⟩
      have hfilt : (Finset.univ.filter
          (fun ω => sameHistory t (trajX C₀ X ω) h ∧ (trajX C₀ X ω).1 t.succ = D)) =
          Finset.univ.filter (fun ω => sameHistory t (trajX C₀ X ω) h ∧ ω t = jj) := by
        apply Finset.filter_congr
        intro ω _
        rw [hsucc]
        constructor
        · rintro ⟨hω, hω2⟩
          refine ⟨hω, ?_⟩
          rw [hval ω hω, ← hjD] at hω2
          exact Fin.ext ((halvesList_nodup _).getElem_inj_iff.mp hω2)
        · rintro ⟨hω, hω2⟩
          refine ⟨hω, ?_⟩
          rw [hval ω hω, ← hjD]
          simp only [hω2, jj]
      rw [hfilt, ← slice_card (fun ω => sameHistory t (trajX C₀ X ω) h) t hP jj, hcard]
      have hN : (Nat.choose (2 ^ (T - t.val)) (2 ^ (T - t.val) / 2) : ℝ≥0∞) =
          (Nn T t.val : ℝ≥0∞) := rfl
      rw [hN]
      have hN0 : (Nn T t.val : ℝ≥0∞) ≠ 0 := by
        have := Nn_pos T t.val; exact_mod_cast this.ne'
      have hNt : (Nn T t.val : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
      push_cast
      rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, mul_right_comm _ _ (Nn T t.val : ℝ≥0∞)⁻¹,
        mul_assoc _ (Nn T t.val : ℝ≥0∞), ENNReal.mul_inv_cancel hN0 hNt, mul_one]
    · have hfilt : (Finset.univ.filter
          (fun ω => sameHistory t (trajX C₀ X ω) h ∧ (trajX C₀ X ω).1 t.succ = D)) = ∅ := by
        apply Finset.filter_false_of_mem
        rintro ω - ⟨hω, hω2⟩
        apply hD
        rw [← mem_halvesList, ← hω2, hsucc, hval ω hω]
        exact List.getElem_mem _
      rw [hfilt]; simp
  · push Not at hne
    have h1 : (Finset.univ.filter
        (fun ω => sameHistory t (trajX C₀ X ω) h ∧ (trajX C₀ X ω).1 t.succ = D)) = ∅ :=
      Finset.filter_false_of_mem (fun ω _ hω => hne ω hω.1)
    have h2 : (Finset.univ.filter (fun ω => sameHistory t (trajX C₀ X ω) h)) = ∅ :=
      Finset.filter_false_of_mem (fun ω _ hω => hne ω hω)
    rw [h1, h2]; simp

theorem halvingX (C₀ : Family m) {T : ℕ} (X : Omega T → ℕ → Finset (Fin m))
    (hX : ∀ ω (t : Fin T) (j : Fin (Nn T t.val)) (s : ℕ), s ≤ t.val →
      X (Function.update ω t j) s = X ω s)
    (hmono : ∀ ω (s : ℕ), s < T → X ω s ⊆ X ω (s + 1))
    (hC : C₀.card = 2 ^ T) : HalvingProcess (pAX C₀ T X) C₀ := by
  refine ⟨?_, ?_, fun t h D => halving_eq C₀ X hX hC t h D⟩
  · intro z hz
    obtain ⟨ω, rfl⟩ := mem_support_pAX C₀ T X z hz
    rfl
  · intro z hz t
    obtain ⟨ω, rfl⟩ := mem_support_pAX C₀ T X z hz
    exact hmono ω t.val t.isLt

theorem terminal_pAX (C₀ : Family m) (T : ℕ) (X : Omega T → ℕ → Finset (Fin m)) :
    terminalExpectation (pAX C₀ T X) =
      ∑ ω : Omega T, (Fintype.card (Omega T) : ℝ)⁻¹ * ((X ω T).card : ℝ) := by
  unfold pAX
  rw [terminal_map]
  rfl

end Law

theorem pmf_sum_toReal {α : Type*} [Fintype α] (p : PMF α) : ∑ a, (p a).toReal = 1 := by
  have h := p.tsum_coe
  rw [tsum_fintype] at h
  rw [← ENNReal.toReal_sum (fun a _ => p.apply_ne_top a), h, ENNReal.toReal_one]

end RandOnlineSetCoverSqrt.Dev.T14A
end

section
set_option autoImplicit false

namespace RandOnlineSetCoverSqrt.Dev.T14B

open Finset

/-! ### Counting permutations: a fixed position, and avoiding a set on an initial segment -/

section Perm

variable {N : ℕ}

/-- All positions are equally likely to receive a fixed request. -/
theorem perm_card_eq (i : Fin N) (h h' : Fin N) :
    (univ.filter (fun π : Equiv.Perm (Fin N) => π i = h)).card =
      (univ.filter (fun π : Equiv.Perm (Fin N) => π i = h')).card := by
  apply Finset.card_nbij' (fun π => Equiv.swap h h' * π) (fun π => Equiv.swap h h' * π)
  · intro π hπ
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hπ ⊢
    simp [hπ]
  · intro π hπ
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hπ ⊢
    simp [hπ]
  · intro π _
    simp [← mul_assoc]
  · intro π _
    simp [← mul_assoc]

theorem perm_card_eq_mul (i : Fin N) (h : Fin N) :
    (univ.filter (fun π : Equiv.Perm (Fin N) => π i = h)).card * N = N.factorial := by
  have hfib := Finset.card_eq_sum_card_fiberwise (s := (univ : Finset (Equiv.Perm (Fin N))))
    (t := (univ : Finset (Fin N))) (f := fun π => π i) (fun _ _ => mem_coe.mpr (mem_univ _))
  rw [card_univ, Fintype.card_perm, Fintype.card_fin] at hfib
  rw [hfib, Finset.sum_congr rfl (fun b _ => perm_card_eq i b h), sum_const, card_univ,
    Fintype.card_fin, smul_eq_mul, mul_comm]

/-- `P(π i ∈ H) = |H| / N`, in multiplied form. -/
theorem perm_card_mem (i : Fin N) (H : Finset (Fin N)) :
    (univ.filter (fun π : Equiv.Perm (Fin N) => π i ∈ H)).card * N = H.card * N.factorial := by
  have hfib := Finset.card_eq_sum_card_fiberwise
    (s := univ.filter (fun π : Equiv.Perm (Fin N) => π i ∈ H)) (t := H) (f := fun π => π i)
    (fun π hπ => by simpa using hπ)
  have hsl : ∀ b ∈ H, ((univ.filter (fun π : Equiv.Perm (Fin N) => π i ∈ H)).filter
      (fun π => π i = b)).card = (univ.filter (fun π : Equiv.Perm (Fin N) => π i = b)).card := by
    intro b hb
    rw [filter_filter]
    congr 1
    apply filter_congr
    intro π _
    constructor
    · exact fun h => h.2
    · intro h; exact ⟨h ▸ hb, h⟩
  rw [hfib, sum_congr rfl hsl, sum_mul]
  rw [sum_congr rfl (fun b _ => perm_card_eq_mul i b), sum_const, smul_eq_mul]

/-- Permutations sending every position `< j` outside `G`. -/
noncomputable def avoid (G : Finset (Fin N)) (j : ℕ) : Finset (Equiv.Perm (Fin N)) :=
  univ.filter (fun π => ∀ i : Fin N, i.val < j → π i ∉ G)

theorem avoid_zero (G : Finset (Fin N)) : (avoid G 0).card = N.factorial := by
  unfold avoid
  rw [filter_true_of_mem (fun π _ i hi => absurd hi (Nat.not_lt_zero _)), card_univ,
    Fintype.card_perm, Fintype.card_fin]

/-- Moving the test position by a transposition. -/
theorem avoid_slice (G : Finset (Fin N)) (j : ℕ) (hj : j < N) (i : Fin N) (hi : j ≤ i.val) :
    ((avoid G j).filter (fun π => π i ∉ G)).card = (avoid G (j + 1)).card := by
  set jj : Fin N := ⟨j, hj⟩
  have key : ∀ (π : Equiv.Perm (Fin N)) (x : Fin N), x.val < j →
      (π * Equiv.swap i jj) x = π x := by
    intro π x hx
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne]
    · intro h; subst h; omega
    · intro h; subst h; simp [jj] at hx
  apply Finset.card_nbij' (fun π => π * Equiv.swap i jj) (fun π => π * Equiv.swap i jj)
  · intro π hπ
    simp only [avoid, coe_filter, mem_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hπ ⊢
    intro x hx
    rcases Nat.lt_succ_iff_lt_or_eq.mp hx with hx | hx
    · rw [key π x hx]; exact hπ.1 x hx
    · have : x = jj := Fin.ext hx
      subst this
      simpa [Equiv.Perm.mul_apply] using hπ.2
  · intro π hπ
    simp only [avoid, coe_filter, mem_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hπ ⊢
    refine ⟨fun x hx => ?_, ?_⟩
    · rw [key π x hx]; exact hπ x (by omega)
    · simpa [Equiv.Perm.mul_apply] using hπ jj (by simp [jj])
  · intro π _
    simp [mul_assoc]
  · intro π _
    simp [mul_assoc]

theorem card_notMem (G : Finset (Fin N)) (π : Equiv.Perm (Fin N)) :
    (univ.filter (fun i => π i ∉ G)).card = N - G.card := by
  have : (univ.filter (fun i => π i ∉ G)) = (Gᶜ).map π.symm.toEmbedding := by
    ext i
    simp only [mem_filter, mem_univ, true_and, mem_map, mem_compl, Equiv.coe_toEmbedding]
    constructor
    · intro h; exact ⟨π i, h, by simp⟩
    · rintro ⟨a, ha, rfl⟩; simpa using ha
  rw [this, card_map, card_compl, Fintype.card_fin]

theorem avoid_step (G : Finset (Fin N)) (j : ℕ) (hj : j < N) :
    N * (avoid G (j + 1)).card ≤ (N - G.card) * (avoid G j).card := by
  classical
  -- double count pairs (π, i) with π ∈ avoid G j, j ≤ i, π i ∉ G
  set S := univ.filter (fun i : Fin N => j ≤ i.val)
  have hS : S.card = N - j := by
    have h1 := Fin.card_filter_val_lt (n := N) (m := j)
    have h2 := card_filter_add_card_filter_not (s := (univ : Finset (Fin N)))
      (fun i : Fin N => i.val < j)
    rw [card_univ, Fintype.card_fin] at h2
    have h3 : (univ.filter (fun i : Fin N => ¬ i.val < j)) = S := by
      apply filter_congr; intro i _; omega
    rw [h3] at h2
    omega
  have hcount : ∑ i ∈ S, ((avoid G j).filter (fun π => π i ∉ G)).card =
      ∑ π ∈ avoid G j, (S.filter (fun i => π i ∉ G)).card := by
    simp only [card_filter]
    exact sum_comm
  have hlhs : ∑ i ∈ S, ((avoid G j).filter (fun π => π i ∉ G)).card =
      (N - j) * (avoid G (j + 1)).card := by
    rw [sum_congr rfl (fun i hi => avoid_slice G j hj i (by simpa [S] using hi)), sum_const, hS,
      smul_eq_mul]
  have hrhs : ∀ π ∈ avoid G j, (S.filter (fun i => π i ∉ G)).card ≤ N - G.card - j := by
    intro π hπ
    simp only [avoid, mem_filter, mem_univ, true_and] at hπ
    have hsplit : (univ.filter (fun i => π i ∉ G)) =
        (univ.filter (fun i : Fin N => i.val < j)) ∪ (S.filter (fun i => π i ∉ G)) := by
      ext i
      simp only [mem_filter, mem_univ, true_and, mem_union, S]
      constructor
      · intro h; by_cases hi : i.val < j
        · exact Or.inl hi
        · exact Or.inr ⟨by omega, h⟩
      · rintro (h | h)
        · exact hπ i h
        · exact h.2
    have hdisj : Disjoint (univ.filter (fun i : Fin N => i.val < j)) (S.filter (fun i => π i ∉ G)) := by
      rw [disjoint_left]
      intro i h1 h2
      simp only [mem_filter, mem_univ, true_and, S] at h1 h2
      omega
    have := card_notMem G π
    rw [hsplit, card_union_of_disjoint hdisj, Fin.card_filter_val_lt] at this
    have hmin : min N j = j := min_eq_right hj.le
    rw [hmin] at this
    omega
  have hle : (N - j) * (avoid G (j + 1)).card ≤ (N - G.card - j) * (avoid G j).card := by
    rw [← hlhs, hcount]
    calc ∑ π ∈ avoid G j, (S.filter (fun i => π i ∉ G)).card
        ≤ ∑ _π ∈ avoid G j, (N - G.card - j) := sum_le_sum hrhs
      _ = _ := by rw [sum_const, smul_eq_mul, mul_comm]
  -- conclude
  set a := (avoid G (j + 1)).card
  set b := (avoid G j).card
  set g := G.card
  have hNj : 0 < N - j := by omega
  have key : (N - j) * (N * a) ≤ (N - j) * ((N - g) * b) := by
    calc (N - j) * (N * a) = N * ((N - j) * a) := by ring
      _ ≤ N * ((N - g - j) * b) := Nat.mul_le_mul_left _ hle
      _ ≤ (N - j) * ((N - g) * b) := by
        rcases le_or_gt (g + j) N with hgj | hgj
        · obtain ⟨u, hu⟩ : ∃ u, N = g + j + u := ⟨N - (g + j), by omega⟩
          have e1 : N - g - j = u := by omega
          have e2 : N - g = j + u := by omega
          have e3 : N - j = g + u := by omega
          rw [e1, e2, e3, hu]
          have : (g + j + u) * u ≤ (g + u) * (j + u) := by nlinarith
          calc (g + j + u) * (u * b) = ((g + j + u) * u) * b := by ring
            _ ≤ ((g + u) * (j + u)) * b := Nat.mul_le_mul_right _ this
            _ = (g + u) * ((j + u) * b) := by ring
        · have : N - g - j = 0 := by omega
          rw [this]; simp
  exact Nat.le_of_mul_le_mul_left key hNj

theorem avoid_bound (G : Finset (Fin N)) (τ : ℕ) (hτ : τ ≤ N) :
    N ^ τ * (avoid G τ).card ≤ (N - G.card) ^ τ * N.factorial := by
  induction τ with
  | zero => simp [avoid_zero]
  | succ τ ih =>
    have h1 := avoid_step G τ (by omega)
    have h2 := ih (by omega)
    calc N ^ (τ + 1) * (avoid G (τ + 1)).card = N ^ τ * (N * (avoid G (τ + 1)).card) := by ring
      _ ≤ N ^ τ * ((N - G.card) * (avoid G τ).card) := Nat.mul_le_mul_left _ h1
      _ = (N - G.card) * (N ^ τ * (avoid G τ).card) := by ring
      _ ≤ (N - G.card) * ((N - G.card) ^ τ * N.factorial) := Nat.mul_le_mul_left _ h2
      _ = (N - G.card) ^ (τ + 1) * N.factorial := by ring

/-- Real form: the avoiding fraction is at most `exp(-|G| τ / N)`. -/
theorem avoid_bound_exp (G : Finset (Fin N)) (τ : ℕ) (hτ : τ ≤ N) (hN : 0 < N) :
    ((avoid G τ).card : ℝ) ≤ N.factorial * Real.exp (-(G.card : ℝ) * τ / N) := by
  have h := avoid_bound G τ hτ
  have hgN : G.card ≤ N := by
    have := card_le_univ G; simpa using this
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hcast : ((N - G.card : ℕ) : ℝ) = N - G.card := by push_cast [Nat.cast_sub hgN]; ring
  have h' : (N : ℝ) ^ τ * (avoid G τ).card ≤ ((N : ℝ) - G.card) ^ τ * N.factorial := by
    have := (Nat.cast_le (α := ℝ)).mpr h
    push_cast [Nat.cast_sub hgN] at this
    exact this
  have hbase : (N : ℝ) - G.card = N * (1 - G.card / N) := by field_simp
  rw [hbase, mul_pow] at h'
  have hpow : 0 < (N : ℝ) ^ τ := by positivity
  have h2 : ((avoid G τ).card : ℝ) ≤ (1 - G.card / N) ^ τ * N.factorial := by
    have := h'
    rw [mul_assoc] at this
    exact le_of_mul_le_mul_left this hpow
  have h3 : (1 - (G.card : ℝ) / N) ^ τ ≤ Real.exp (-(G.card : ℝ) * τ / N) := by
    have hnn : 0 ≤ 1 - (G.card : ℝ) / N := by
      rw [sub_nonneg, div_le_one hNr]; exact_mod_cast hgN
    have hle : 1 - (G.card : ℝ) / N ≤ Real.exp (-(G.card / N)) := by
      have := Real.add_one_le_exp (-(G.card / N : ℝ)); linarith
    calc (1 - (G.card : ℝ) / N) ^ τ ≤ Real.exp (-(G.card / N)) ^ τ :=
          pow_le_pow_left₀ hnn hle τ
      _ = Real.exp (-(G.card : ℝ) * τ / N) := by
          rw [← Real.exp_nat_mul]; congr 1; ring
  calc ((avoid G τ).card : ℝ) ≤ (1 - G.card / N) ^ τ * N.factorial := h2
    _ ≤ Real.exp (-(G.card : ℝ) * τ / N) * N.factorial :=
        mul_le_mul_of_nonneg_right h3 (by positivity)
    _ = _ := by ring

end Perm

/-! ### Binomial coefficient estimates -/

section Choose

theorem choose_double (v b j : ℕ) (h : 3 * (b + j) + 2 ≤ v) :
    Nat.choose v b * 2 ^ j ≤ Nat.choose v (b + j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have ih' := ih (by omega)
    have hs := Nat.choose_succ_right_eq v (b + j)
    have hstep : 2 * Nat.choose v (b + j) ≤ Nat.choose v (b + j + 1) := by
      have hpos : 0 < b + j + 1 := by omega
      have : 2 * Nat.choose v (b + j) * (b + j + 1) ≤ Nat.choose v (b + j + 1) * (b + j + 1) := by
        rw [hs]
        have : 2 * (b + j + 1) ≤ v - (b + j) := by omega
        calc 2 * Nat.choose v (b + j) * (b + j + 1) = Nat.choose v (b + j) * (2 * (b + j + 1)) := by
              ring
          _ ≤ Nat.choose v (b + j) * (v - (b + j)) := Nat.mul_le_mul_left _ this
      exact Nat.le_of_mul_le_mul_right this hpos
    calc Nat.choose v b * 2 ^ (j + 1) = 2 * (Nat.choose v b * 2 ^ j) := by ring
      _ ≤ 2 * Nat.choose v (b + j) := Nat.mul_le_mul_left _ ih'
      _ ≤ Nat.choose v (b + j + 1) := hstep
      _ = Nat.choose v (b + (j + 1)) := by rw [Nat.add_assoc]

theorem choose_mono_of (v b b' : ℕ) (hb : b ≤ b') (h : 3 * b' + 2 ≤ v) :
    Nat.choose v b ≤ Nat.choose v b' := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hb
  have := choose_double v b j h
  calc Nat.choose v b ≤ Nat.choose v b * 2 ^ j := Nat.le_mul_of_pos_right _ (by positivity)
    _ ≤ _ := this

theorem choose_avoid (v β y : ℕ) (hy : y ≤ v) (h : 4 * β ≤ 3 * (v - y + 1)) :
    Nat.choose v β ≤ 4 ^ y * Nat.choose (v - y) β := by
  induction y with
  | zero => simp
  | succ y ih =>
    have ih' := ih (by omega) (by omega)
    -- n := v - y - 1, n + 1 = v - y
    set n := v - (y + 1) with hn
    have hn1 : v - y = n + 1 := by omega
    have hc := Nat.choose_mul_succ_eq n β
    have hβ : β < n + 1 := by omega
    have hstep : Nat.choose (n + 1) β ≤ 4 * Nat.choose n β := by
      have hpos : 0 < n + 1 - β := by omega
      have : Nat.choose (n + 1) β * (n + 1 - β) ≤ 4 * Nat.choose n β * (n + 1 - β) := by
        rw [← hc]
        have : n + 1 ≤ 4 * (n + 1 - β) := by omega
        calc Nat.choose n β * (n + 1) ≤ Nat.choose n β * (4 * (n + 1 - β)) :=
              Nat.mul_le_mul_left _ this
          _ = 4 * Nat.choose n β * (n + 1 - β) := by ring
      exact Nat.le_of_mul_le_mul_right this hpos
    rw [hn1] at ih'
    calc Nat.choose v β ≤ 4 ^ y * Nat.choose (n + 1) β := ih'
      _ ≤ 4 ^ y * (4 * Nat.choose n β) := Nat.mul_le_mul_left _ hstep
      _ = 4 ^ (y + 1) * Nat.choose n β := by ring

end Choose

end RandOnlineSetCoverSqrt.Dev.T14B
end

section
set_option autoImplicit false

open scoped ENNReal

namespace RandOnlineSetCoverSqrt.Dev.T14C
open RandOnlineSetCoverSqrt.LowerBound RandOnlineSetCover.InfoLB
open RandOnlineSetCoverSqrt.LowerBound.Supplement
open RandOnlineSetCoverSqrt.Dev.T14A RandOnlineSetCoverSqrt.Dev.T14B
open Finset

/-! ### Regions of `Fin m`: core `[0,d)`, encoding `[d,2d)`, `V = [2d, 2d+v)` -/

section Regions

variable {d v m : ℕ} (h : 2 * d + v ≤ m)

def eC : Fin d ↪ Fin m :=
  ⟨fun i => ⟨i.val, by have := i.isLt; omega⟩, fun a b hab => by
    simp only [Fin.mk.injEq] at hab; exact Fin.ext hab⟩

def eE : Fin d ↪ Fin m :=
  ⟨fun i => ⟨d + i.val, by have := i.isLt; omega⟩, fun a b hab => by
    simp only [Fin.mk.injEq] at hab; exact Fin.ext (by omega)⟩

def eV : Fin v ↪ Fin m :=
  ⟨fun i => ⟨2 * d + i.val, by have := i.isLt; omega⟩, fun a b hab => by
    simp only [Fin.mk.injEq] at hab; exact Fin.ext (by omega)⟩

theorem eC_val (i : Fin d) : (eC h i).val = i.val := rfl
theorem eE_val (i : Fin d) : (eE h i).val = d + i.val := rfl
theorem eV_val (i : Fin v) : (eV h i).val = 2 * d + i.val := rfl

theorem eC_ne_eE (a b : Fin d) : eC h a ≠ eE h b := by
  intro hab; have := congrArg Fin.val hab; rw [eC_val, eE_val] at this; have := a.isLt; omega

theorem eC_ne_eV (a : Fin d) (b : Fin v) : eC h a ≠ eV h b := by
  intro hab; have := congrArg Fin.val hab; rw [eC_val, eV_val] at this; have := a.isLt; omega

theorem eE_ne_eV (a : Fin d) (b : Fin v) : eE h a ≠ eV h b := by
  intro hab; have := congrArg Fin.val hab; rw [eE_val, eV_val] at this; have := a.isLt; omega

theorem eV_notMem_mapC (b : Fin v) (S : Finset (Fin d)) : eV h b ∉ S.map (eC h) := by
  simp only [mem_map, not_exists, not_and]
  intro a _ hab; exact eC_ne_eV h a b hab

theorem eV_notMem_mapE (b : Fin v) (S : Finset (Fin d)) : eV h b ∉ S.map (eE h) := by
  simp only [mem_map, not_exists, not_and]
  intro a _ hab; exact eE_ne_eV h a b hab

theorem eE_notMem_mapC (b : Fin d) (S : Finset (Fin d)) : eE h b ∉ S.map (eC h) := by
  simp only [mem_map, not_exists, not_and]
  intro a _ hab; exact eC_ne_eE h a b hab

theorem eE_notMem_mapV (b : Fin d) (S : Finset (Fin v)) : eE h b ∉ S.map (eV h) := by
  simp only [mem_map, not_exists, not_and]
  intro a _ hab; exact eE_ne_eV h b a hab.symm

theorem eC_notMem_mapV (b : Fin d) (S : Finset (Fin v)) : eC h b ∉ S.map (eV h) := by
  simp only [mem_map, not_exists, not_and]
  intro a _ hab; exact eC_ne_eV h b a hab.symm

/-- The parts of a label in the three regions. -/
def partC (S : Finset (Fin m)) : Finset (Fin d) := univ.filter (fun i => eC h i ∈ S)
def partE (S : Finset (Fin m)) : Finset (Fin d) := univ.filter (fun i => eE h i ∈ S)
def partV (S : Finset (Fin m)) : Finset (Fin v) := univ.filter (fun i => eV h i ∈ S)

theorem partC_real (A : Finset (Fin d)) (R : Finset (Fin v)) :
    partC h (A.map (eC h) ∪ R.map (eV h)) = A := by
  ext i; simp [partC, eC_notMem_mapV h]

theorem partE_real (A : Finset (Fin d)) (R : Finset (Fin v)) :
    partE h (A.map (eC h) ∪ R.map (eV h)) = ∅ := by
  ext i; simp [partE, eE_notMem_mapC h, eE_notMem_mapV h]

theorem partV_real (A : Finset (Fin d)) (R : Finset (Fin v)) :
    partV h (A.map (eC h) ∪ R.map (eV h)) = R := by
  ext i; simp [partV, eV_notMem_mapC h]

theorem partE_dummy (A : Finset (Fin d)) (R : Finset (Fin v)) :
    partE h (univ.map (eC h) ∪ A.map (eE h) ∪ R.map (eV h)) = A := by
  ext i; simp [partE, eE_notMem_mapC h, eE_notMem_mapV h]

theorem partV_dummy (A : Finset (Fin d)) (R : Finset (Fin v)) :
    partV h (univ.map (eC h) ∪ A.map (eE h) ∪ R.map (eV h)) = R := by
  ext i; simp [partV, eV_notMem_mapC h, eV_notMem_mapE h]

theorem card_partC_le (S : Finset (Fin m)) : (partC h S).card ≤ S.card := by
  apply card_le_card_of_injOn (eC h)
  · intro i hi; simpa [partC] using hi
  · intro a _ b _ hab; exact (eC h).injective hab

theorem card_partV_le (S : Finset (Fin m)) : (partV h S).card ≤ S.card := by
  apply card_le_card_of_injOn (eV h)
  · intro i hi; simpa [partV] using hi
  · intro a _ b _ hab; exact (eV h).injective hab

end Regions

/-! ### Requests, the chain, the instance -/

/-- Requests: a level `t`, a label `A` of the core, a set `R ⊆ V` of size `β t`. -/
def J (T d v : ℕ) (β : ℕ → ℕ) :=
  {j : Fin T × Element d × Finset (Fin v) // j.2.2.card = β j.1.val}

instance (T d v : ℕ) (β : ℕ → ℕ) : Fintype (J T d v β) := by unfold J; infer_instance
instance (T d v : ℕ) (β : ℕ → ℕ) : DecidableEq (J T d v β) := by unfold J; infer_instance

noncomputable def NN (T d v : ℕ) (β : ℕ → ℕ) : ℕ := Fintype.card (J T d v β)

noncomputable def enum (T d v : ℕ) (β : ℕ → ℕ) : J T d v β ≃ Fin (NN T d v β) :=
  Fintype.equivFin _

section Construction

variable {T d v m : ℕ} {β : ℕ → ℕ} (h : 2 * d + v ≤ m)

/-- The embedded copy of the core family. -/
def C0' (C₀ : Family d) : Family m := C₀.map (Finset.mapEmbedding (eC h)).toEmbedding

/-- Pull back a family on `Fin m` to the core. -/
def pull (F : Family m) : Family d := univ.filter (fun W => W.map (eC h) ∈ F)

noncomputable def bat (r : ℕ) (C₀ : Family d) (ω : Omega T) (t : ℕ) : List (Element d) :=
  batch r (pull h (cN (C0' h C₀) ω t))

/-- The label of a request: real (`A ∪ R`) if `A` is in the batch of its level, else dummy. -/
noncomputable def incid (r : ℕ) (C₀ : Family d) (ω : Omega T) (j : J T d v β) : Finset (Fin m) :=
  if j.val.2.1 ∈ bat h r C₀ ω j.val.1.val then
    j.val.2.1.val.map (eC h) ∪ j.val.2.2.map (eV h)
  else univ.map (eC h) ∪ j.val.2.1.val.map (eE h) ∪ j.val.2.2.map (eV h)

theorem incid_nonempty (r : ℕ) (C₀ : Family d) (ω : Omega T) (j : J T d v β) :
    (incid h r C₀ ω j).Nonempty := by
  unfold incid
  obtain ⟨a, ha⟩ := j.val.2.1.property
  split_ifs
  · exact ⟨eC h a, mem_union_left _ (mem_map_of_mem _ ha)⟩
  · exact ⟨eE h a, mem_union_left _ (mem_union_right _ (mem_map_of_mem _ ha))⟩

theorem incid_congr (r : ℕ) (C₀ : Family d) (ω ω' : Omega T) (j : J T d v β)
    (hc : cN (C0' h C₀) ω j.val.1.val = cN (C0' h C₀) ω' j.val.1.val) :
    incid h r C₀ ω j = incid h r C₀ ω' j := by
  unfold incid bat
  rw [hc]

theorem incid_injective (r : ℕ) (C₀ : Family d) (ω : Omega T)
    (hβ : ∀ t t', t < T → t' < T → β t = β t' → t = t') :
    Function.Injective (incid (β := β) h r C₀ ω) := by
  intro j j' hjj
  have hR : j.val.2.2 = j'.val.2.2 := by
    have := congrArg (partV h) hjj
    unfold incid at this
    split_ifs at this
    · rwa [partV_real, partV_real] at this
    · rwa [partV_real, partV_dummy] at this
    · rwa [partV_dummy, partV_real] at this
    · rwa [partV_dummy, partV_dummy] at this
  have ht : j.val.1 = j'.val.1 := by
    have h1 := j.property
    have h2 := j'.property
    rw [hR] at h1
    exact Fin.ext (hβ _ _ j.val.1.isLt j'.val.1.isLt (h1.symm.trans h2))
  have hA : j.val.2.1 = j'.val.2.1 := by
    have hE := congrArg (partE h) hjj
    have hC := congrArg (partC h) hjj
    unfold incid at hE hC
    rw [← ht] at hE hC
    split_ifs at hE hC with h1 h2 h2
    · rw [partC_real, partC_real] at hC; exact Subtype.ext hC
    · rw [partE_real, partE_dummy] at hE
      exact absurd hE.symm (Finset.nonempty_iff_ne_empty.mp j'.val.2.1.property)
    · rw [partE_real, partE_dummy] at hE
      exact absurd hE (Finset.nonempty_iff_ne_empty.mp j.val.2.1.property)
    · rw [partE_dummy, partE_dummy] at hE; exact Subtype.ext hE
  apply Subtype.ext
  exact Prod.ext ht (Prod.ext hA hR)

/-- The instance (requests listed in the fixed enumeration). -/
noncomputable def inst (r : ℕ) (C₀ : Family d) (ω : Omega T) : Instance m (NN T d v β) :=
  ⟨fun i => incid h r C₀ ω ((enum T d v β).symm i), fun i => incid_nonempty h r C₀ ω _⟩

theorem inst_distinct (r : ℕ) (C₀ : Family d) (ω : Omega T)
    (hβ : ∀ t t', t < T → t' < T → β t = β t' → t = t') :
    DistinctRequests (inst (β := β) h r C₀ ω) := by
  intro i i' hii
  have := incid_injective h r C₀ ω hβ hii
  exact (enum T d v β).symm.injective this

/-! #### The core family and its pullbacks -/

theorem mem_C0' (C₀ : Family d) (V : Candidate m) :
    V ∈ C0' h C₀ ↔ ∃ W ∈ C₀, W.map (eC h) = V := by
  simp [C0', Finset.mem_map]

theorem card_C0' (C₀ : Family d) : (C0' h C₀).card = C₀.card := by
  simp [C0']

theorem mem_pull (F : Family m) (W : Finset (Fin d)) : W ∈ pull h F ↔ W.map (eC h) ∈ F := by
  simp [pull]

theorem pull_sub (C₀ : Family d) (F : Family m) (hF : F ⊆ C0' h C₀) : pull h F ⊆ C₀ := by
  intro W hW
  rw [mem_pull] at hW
  obtain ⟨W', hW', he⟩ := (mem_C0' h C₀ _).mp (hF hW)
  have : W' = W := Finset.map_injective (eC h) he
  rw [← this]; exact hW'

theorem pull_nonempty (C₀ : Family d) (F : Family m) (hF : F ⊆ C0' h C₀) (hne : F.Nonempty) :
    (pull h F).Nonempty := by
  obtain ⟨V, hV⟩ := hne
  obtain ⟨W, _, rfl⟩ := (mem_C0' h C₀ _).mp (hF hV)
  exact ⟨W, (mem_pull h F W).mpr hV⟩

/-- Forcing for the batch of level `t`. -/
theorem bat_forcing (r : ℕ) (C₀ : Family d) (hC : C₀.card = 2 ^ T)
    (hne : ∀ W ∈ C₀, W.Nonempty) (hr : 1 ≤ r) (ω : Omega T) (t : ℕ) (ht : t ≤ T) :
    Forcing r (pull h (cN (C0' h C₀) ω t)) (bat h r C₀ ω t) := by
  have hc := cN_card (C0' h C₀) (by rw [card_C0', hC]) ω t ht
  apply batch_forcing
  · apply pull_nonempty h C₀ _ hc.2
    exact Finset.card_pos.mp (by rw [hc.1]; positivity)
  · intro W hW; exact hne W (pull_sub h C₀ _ hc.2 hW)
  · exact hr

/-! #### Optimum -/

theorem opt_bounds (r k : ℕ) (C₀ : Family d) (hC : C₀.card = 2 ^ T)
    (hk : ∀ W ∈ C₀, W.card = k) (hk1 : 1 ≤ k) (hkr : k ≤ r) (ω : Omega T)
    (hN : 0 < NN T d v β) :
    1 ≤ Opt (inst (β := β) h r C₀ ω) ∧ Opt (inst (β := β) h r C₀ ω) ≤ k := by
  have hC' : (C0' h C₀).card = 2 ^ T := by rw [card_C0', hC]
  have hne : ∀ W ∈ C₀, W.Nonempty := fun W hW => Finset.card_pos.mp (by rw [hk W hW]; omega)
  have hT := cN_card (C0' h C₀) hC' ω T le_rfl
  rw [Nat.sub_self, pow_zero] at hT
  obtain ⟨V, hV⟩ := Finset.card_eq_one.mp hT.1
  have hVT : V ∈ cN (C0' h C₀) ω T := by rw [hV]; exact Finset.mem_singleton_self V
  obtain ⟨W, hW, rfl⟩ := (mem_C0' h C₀ V).mp (hT.2 hVT)
  have hWk : W.card = k := hk W hW
  have hWne : W.Nonempty := hne W hW
  have hcov : Covers (List.ofFn (inst (β := β) h r C₀ ω).val) (W.map (eC h)) := by
    intro e he
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp he
    set j := (enum T d v β).symm i
    show (W.map (eC h) ∩ incid h r C₀ ω j).Nonempty
    unfold incid
    split_ifs with hA
    · have hu : j.val.1.val ≤ T := j.val.1.isLt.le
      have hF := bat_forcing h r C₀ hC hne (by omega) ω _ hu
      have hWu : W ∈ pull h (cN (C0' h C₀) ω j.val.1.val) := by
        rw [mem_pull]
        exact cN_antitone (C0' h C₀) hC' ω _ T hu le_rfl hVT
      have hcb := (hF W (by omega)).mpr ⟨W, hWu, subset_rfl⟩
      obtain ⟨a, ha⟩ := hcb j.val.2.1.val (List.mem_map_of_mem hA)
      rw [mem_inter] at ha
      exact ⟨eC h a, mem_inter.mpr ⟨mem_map_of_mem _ ha.1,
        mem_union_left _ (mem_map_of_mem _ ha.2)⟩⟩
    · obtain ⟨a, ha⟩ := hWne
      exact ⟨eC h a, mem_inter.mpr ⟨mem_map_of_mem _ ha,
        mem_union_left _ (mem_union_left _ (mem_map_of_mem _ (mem_univ _)))⟩⟩
  have hle : listOpt (List.ofFn (inst (β := β) h r C₀ ω).val) ≤ k := by
    unfold listOpt
    exact iInf_le_of_le ⟨_, hcov⟩ (by simp [hWk])
  have hge : 1 ≤ listOpt (List.ofFn (inst (β := β) h r C₀ ω).val) := by
    unfold listOpt
    refine le_iInf fun C => ?_
    have he : (inst (β := β) h r C₀ ω).val ⟨0, hN⟩ ∈ List.ofFn (inst (β := β) h r C₀ ω).val :=
      List.mem_ofFn.mpr ⟨_, rfl⟩
    obtain ⟨x, hx⟩ := C.2 _ he
    have : 1 ≤ C.val.card := Finset.card_pos.mpr ⟨x, (Finset.mem_inter.mp hx).1⟩
    exact_mod_cast this
  have hnt : listOpt (List.ofFn (inst (β := β) h r C₀ ω).val) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.natCast_ne_top k) hle
  refine ⟨?_, ENat.toNat_le_of_le_natCast hle⟩
  unfold Opt
  have h' := ENat.natCast_toNat hnt
  rw [← h'] at hge
  exact_mod_cast hge

/-! #### The purchase process for a fixed arrival order -/

/-- Prefix lengths: `τ t` for `t < T`, everything at `T`. -/
noncomputable def tauT (τ : ℕ → ℕ) (s : ℕ) : ℕ := if s < T then τ s else NN T d v β

noncomputable def arr (r : ℕ) (C₀ : Family d) (π : Equiv.Perm (Fin (NN T d v β))) (ω : Omega T) :
    List (Finset (Fin m)) :=
  List.ofFn (reorder (inst (β := β) h r C₀ ω) π).val

noncomputable def Xp (r : ℕ) (C₀ : Family d) (τ : ℕ → ℕ) (A : DetAlg m (NN T d v β))
    (π : Equiv.Perm (Fin (NN T d v β))) (ω : Omega T) (s : ℕ) : Finset (Fin m) :=
  chosen A.val ((arr h r C₀ π ω).take (tauT (T := T) (d := d) (v := v) (β := β) τ s))

/-- Level of the request at an index. -/
noncomputable def lev (n : Fin (NN T d v β)) : ℕ := ((enum T d v β).symm n).val.1.val

def goodE (τ : ℕ → ℕ) (π : Equiv.Perm (Fin (NN T d v β))) : Prop :=
  ∀ t, t < T → ∀ i : Fin (NN T d v β), i.val < τ t → lev (π i) ≤ t

noncomputable def GG (t : ℕ) (A : Element d) (Y : Finset (Fin v)) : Finset (Fin (NN T d v β)) :=
  univ.filter (fun n => ((enum T d v β).symm n).val.1.val = t ∧
    ((enum T d v β).symm n).val.2.1 = A ∧ Disjoint ((enum T d v β).symm n).val.2.2 Y)

def goodI (r : ℕ) (τ : ℕ → ℕ) (π : Equiv.Perm (Fin (NN T d v β))) : Prop :=
  ∀ t, t < T → ∀ (A : Element d) (Y : Finset (Fin v)), Y.card ≤ r →
    ∃ i : Fin (NN T d v β), i.val < τ t ∧ π i ∈ GG t A Y

theorem valid_at {n : ℕ} (A : DetAlg m n) (I : Instance m n) (i : Fin n) :
    (chosen A.val ((List.ofFn I.val).take (i.val + 1)) ∩ I.val i).Nonempty := by
  have hval := A.2 ⟨Fin.last n, I.val⟩ ⟨i.val, by simp⟩ (I.2 i)
  simpa using hval

theorem Xp_update (r : ℕ) (C₀ : Family d) (τ : ℕ → ℕ) (A : DetAlg m (NN T d v β))
    (π : Equiv.Perm (Fin (NN T d v β))) (hπ : goodE (T := T) τ π)
    (ω : Omega T) (t : Fin T) (jj : Fin (Nn T t.val)) (s : ℕ) (hs : s ≤ t.val) :
    Xp h r C₀ τ A π (Function.update ω t jj) s = Xp h r C₀ τ A π ω s := by
  unfold Xp
  have hsT : s < T := lt_of_le_of_lt hs t.isLt
  have htk : (arr h r C₀ π (Function.update ω t jj)).take (tauT (T := T) (d := d) (v := v)
      (β := β) τ s) = (arr h r C₀ π ω).take (tauT (T := T) (d := d) (v := v) (β := β) τ s) := by
    simp only [tauT, if_pos hsT]
    apply List.ext_getElem
    · simp [arr]
    · intro i h1 h2
      rw [List.length_take, arr, List.length_ofFn] at h1
      have hi : i < τ s := (lt_min_iff.mp h1).1
      have hin : i < NN T d v β := (lt_min_iff.mp h1).2
      simp only [List.getElem_take, arr, List.getElem_ofFn, reorder, inst]
      have hlev := hπ s hsT ⟨i, hin⟩ hi
      apply incid_congr
      apply cN_congr
      intro u hu
      have : u ≠ t := by
        intro he; subst he; unfold lev at hlev; omega
      simp [Function.update_of_ne this]
  rw [htk]

theorem Xp_mono (r : ℕ) (C₀ : Family d) (τ : ℕ → ℕ) (A : DetAlg m (NN T d v β))
    (π : Equiv.Perm (Fin (NN T d v β)))
    (hτ : ∀ s, s + 1 < T → τ s ≤ τ (s + 1)) (hτN : ∀ s, s < T → τ s ≤ NN T d v β)
    (ω : Omega T) (s : ℕ) (hs : s < T) :
    Xp h r C₀ τ A π ω s ⊆ Xp h r C₀ τ A π ω (s + 1) := by
  unfold Xp
  apply chosen_mono
  apply List.take_prefix_take_left
  simp only [tauT, if_pos hs]
  split_ifs with h1
  · exact hτ s h1
  · exact hτN s hs

theorem Xp_last (r : ℕ) (C₀ : Family d) (τ : ℕ → ℕ) (A : DetAlg m (NN T d v β))
    (π : Equiv.Perm (Fin (NN T d v β))) (ω : Omega T) :
    (Xp h r C₀ τ A π ω T).card = cost A (reorder (inst (β := β) h r C₀ ω) π) := by
  unfold Xp cost listCost
  simp only [tauT, lt_irrefl, if_false, arr]
  rw [List.take_of_length_le (by simp)]

/-- `hwitness` of Lemma 4.1 for a good order. -/
theorem Xp_witness (r : ℕ) (C₀ : Family d) (hC : C₀.card = 2 ^ T)
    (hne : ∀ W ∈ C₀, W.Nonempty) (hr : 1 ≤ r) (τ : ℕ → ℕ) (A : DetAlg m (NN T d v β))
    (π : Equiv.Perm (Fin (NN T d v β))) (hπ : goodI (T := T) r τ π) (ω : Omega T) (t : ℕ)
    (ht : t < T) (hX : (Xp h r C₀ τ A π ω t).card ≤ r) :
    ∃ W ∈ cN (C0' h C₀) ω t, W ⊆ Xp h r C₀ τ A π ω t := by
  set Z := Xp h r C₀ τ A π ω t
  have hF := bat_forcing h r C₀ hC hne hr ω t ht.le
  have hZc : (partC h Z).card ≤ r := (card_partC_le h Z).trans hX
  have hcov : CoversBatch (partC h Z) (bat h r C₀ ω t) := by
    intro e he
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp he
    obtain ⟨i, hi, hG⟩ := hπ t ht u (partV h Z) ((card_partV_le h Z).trans hX)
    simp only [GG, mem_filter, mem_univ, true_and] at hG
    obtain ⟨hlt, hAu, hdis⟩ := hG
    set j := (enum T d v β).symm (π i)
    have hval := valid_at A (reorder (inst (β := β) h r C₀ ω) π) i
    have hsub : chosen A.val ((List.ofFn (reorder (inst (β := β) h r C₀ ω) π).val).take
        (i.val + 1)) ⊆ Z := by
      apply chosen_mono
      apply List.take_prefix_take_left
      simp only [tauT, if_pos ht]; omega
    have hinc : (reorder (inst (β := β) h r C₀ ω) π).val i =
        u.val.map (eC h) ∪ j.val.2.2.map (eV h) := by
      show incid h r C₀ ω j = _
      unfold incid
      rw [if_pos (by rw [hAu, hlt]; exact hu), hAu]
    rw [hinc] at hval
    obtain ⟨y, hy⟩ := hval
    rw [mem_inter, mem_union] at hy
    rcases hy.2 with hy2 | hy2
    · obtain ⟨a, ha, rfl⟩ := mem_map.mp hy2
      exact ⟨a, mem_inter.mpr ⟨by simp [partC, hsub hy.1], ha⟩⟩
    · obtain ⟨b, hb, rfl⟩ := mem_map.mp hy2
      exfalso
      have : b ∈ partV h Z := by simp [partV, hsub hy.1]
      exact Finset.disjoint_left.mp hdis hb this
  obtain ⟨W, hW, hWZ⟩ := (hF _ hZc).mp hcov
  refine ⟨W.map (eC h), (mem_pull h _ W).mp hW, ?_⟩
  intro y hy
  obtain ⟨a, ha, rfl⟩ := mem_map.mp hy
  have := hWZ ha
  simpa [partC] using this

end Construction

end RandOnlineSetCoverSqrt.Dev.T14C
end

section
set_option autoImplicit false

namespace RandOnlineSetCoverSqrt.Dev.T14D
open RandOnlineSetCoverSqrt.LowerBound RandOnlineSetCover.InfoLB
open RandOnlineSetCoverSqrt.Dev.T14A RandOnlineSetCoverSqrt.Dev.T14B RandOnlineSetCoverSqrt.Dev.T14C
open Finset

/-! ### Most arrival orders are good -/

section Good

variable {T d v : ℕ} {β : ℕ → ℕ}

/-- Indices of requests of level `> t`. -/
noncomputable def HH (t : ℕ) : Finset (Fin (NN T d v β)) :=
  univ.filter (fun n => t < lev n)

theorem card_element_le : Fintype.card (Element d) ≤ 2 ^ d := by
  calc Fintype.card (Element d) ≤ Fintype.card (Finset (Fin d)) := Fintype.card_subtype_le _
    _ = 2 ^ d := by rw [Fintype.card_finset, Fintype.card_fin]

theorem card_HH (t Lnext : ℕ) (hL : ∀ t', t < t' → t' < T → Nat.choose v (β t') ≤ Lnext) :
    (HH (T := T) (d := d) (v := v) (β := β) t).card ≤ T * 2 ^ d * Lnext := by
  classical
  set tgt : Finset (Fin T × Element d × Finset (Fin v)) :=
    (univ.filter (fun t' : Fin T => t < t'.val)).biUnion
      (fun t' => (univ ×ˢ powersetCard (β t'.val) (univ : Finset (Fin v))).image (fun p => (t', p)))
  have h1 : (HH (T := T) (d := d) (v := v) (β := β) t).card ≤ tgt.card := by
    apply card_le_card_of_injOn (fun n => ((enum T d v β).symm n).val)
    · intro n hn
      have hn' : t < lev n := (mem_filter.mp (mem_coe.mp hn)).2
      rw [mem_coe, mem_biUnion]
      refine ⟨((enum T d v β).symm n).val.1, mem_filter.mpr ⟨mem_univ _, hn'⟩, ?_⟩
      rw [mem_image]
      exact ⟨((enum T d v β).symm n).val.2, mem_product.mpr ⟨mem_univ _,
        mem_powersetCard.mpr ⟨subset_univ _, ((enum T d v β).symm n).property⟩⟩, rfl⟩
    · intro a _ b _ hab
      exact (enum T d v β).symm.injective (Subtype.ext hab)
  have h2 : tgt.card ≤ T * 2 ^ d * Lnext := by
    refine (card_biUnion_le).trans ?_
    calc ∑ t' ∈ univ.filter (fun t' : Fin T => t < t'.val),
          ((univ ×ˢ powersetCard (β t'.val) (univ : Finset (Fin v))).image
            (fun p => (t', p))).card
        ≤ ∑ _t' ∈ univ.filter (fun t' : Fin T => t < t'.val), 2 ^ d * Lnext := by
          apply sum_le_sum
          intro t' ht'
          simp only [mem_filter, mem_univ, true_and] at ht'
          refine card_image_le.trans ?_
          rw [card_product, card_powersetCard, card_univ, card_univ, Fintype.card_fin]
          exact Nat.mul_le_mul card_element_le (hL t'.val ht' t'.isLt)
      _ ≤ ∑ _t' : Fin T, 2 ^ d * Lnext := sum_le_sum_of_subset (filter_subset _ _)
      _ = T * 2 ^ d * Lnext := by
          rw [sum_const, card_univ, Fintype.card_fin, smul_eq_mul, mul_assoc]
  exact h1.trans h2

theorem card_GG (r t : ℕ) (ht : t < T) (A : Element d) (Y : Finset (Fin v)) (hY : Y.card ≤ r)
    (hrv : r ≤ v) (hcond : 4 * β t ≤ 3 * (v - r + 1)) :
    Nat.choose v (β t) ≤ 4 ^ r * (GG (T := T) (d := d) (v := v) (β := β) t A Y).card := by
  classical
  have hYv : Y.card ≤ v := hY.trans hrv
  have h1 := choose_avoid v (β t) Y.card hYv (by omega)
  have h2 : Nat.choose (v - Y.card) (β t) ≤ (GG (T := T) (d := d) (v := v) (β := β) t A Y).card := by
    have htgt : ((univ \ Y).powersetCard (β t)).card = Nat.choose (v - Y.card) (β t) := by
      rw [card_powersetCard, card_univ_sdiff, Fintype.card_fin]
    rw [← htgt]
    apply card_le_card_of_surjOn (fun n => ((enum T d v β).symm n).val.2.2)
    intro R hR
    rw [mem_coe, mem_powersetCard] at hR
    have hsn : (enum T d v β).symm (enum T d v β ⟨(⟨t, ht⟩, A, R), hR.2⟩) =
        ⟨(⟨t, ht⟩, A, R), hR.2⟩ := Equiv.symm_apply_apply _ _
    refine ⟨enum T d v β ⟨(⟨t, ht⟩, A, R), hR.2⟩, ?_, by simp only [hsn]⟩
    rw [mem_coe, GG, mem_filter, hsn]
    exact ⟨mem_univ _, rfl, rfl, (subset_sdiff.mp hR.1).2⟩
  calc Nat.choose v (β t) ≤ 4 ^ Y.card * Nat.choose (v - Y.card) (β t) := h1
    _ ≤ 4 ^ r * (GG (T := T) (d := d) (v := v) (β := β) t A Y).card :=
        Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) hY) h2

theorem choose_le_NN (t : ℕ) (ht : t < T) (hd : 0 < d) : Nat.choose v (β t) ≤ NN T d v β := by
  have A₀ : Element d := ⟨univ, univ_nonempty_iff.mpr ⟨⟨0, hd⟩⟩⟩
  have := Fintype.card_le_of_injective
    (fun R : {R : Finset (Fin v) // R.card = β t} =>
      (⟨(⟨t, ht⟩, A₀, R.val), R.property⟩ : J T d v β))
    (by intro a b hab; exact Subtype.ext (congrArg (fun j : J T d v β => j.val.2.2) hab))
  rw [Fintype.card_finset_len, Fintype.card_fin] at this
  exact this

open Classical in
/-- The good orders. -/
noncomputable def goodSet (r : ℕ) (τ : ℕ → ℕ) : Finset (Equiv.Perm (Fin (NN T d v β))) :=
  univ.filter (fun π => goodE (T := T) τ π ∧ goodI (T := T) r τ π)

theorem mem_goodSet (r : ℕ) (τ : ℕ → ℕ) (π : Equiv.Perm (Fin (NN T d v β))) :
    π ∈ goodSet r τ ↔ goodE (T := T) τ π ∧ goodI (T := T) r τ π := by
  classical
  simp [goodSet]

theorem good_card (r M : ℕ) (τ : ℕ → ℕ) (hN : 0 < NN T d v β)
    (hτN : ∀ t, t < T → τ t ≤ NN T d v β)
    (hE : 20 * ∑ t ∈ range T, τ t * (HH (T := T) (d := d) (v := v) (β := β) t).card ≤
      NN T d v β)
    (hI : ∀ t, t < T → ∀ (A : Element d) (Y : Finset (Fin v)), Y.card ≤ r →
      M * NN T d v β ≤ (GG (T := T) (d := d) (v := v) (β := β) t A Y).card * τ t)
    (hcount : 32 * (T * 2 ^ d * 2 ^ v) ≤ 2 ^ M) :
    (9 / 10 : ℝ) * (NN T d v β).factorial ≤ (goodSet (T := T) (d := d) (v := v) (β := β) r τ).card := by
  classical
  set N := NN T d v β with hNdef
  let BE : Finset (Equiv.Perm (Fin N)) := (range T).biUnion (fun t =>
    (univ.filter (fun i : Fin N => i.val < τ t)).biUnion
      (fun i => univ.filter (fun π : Equiv.Perm (Fin N) =>
        π i ∈ HH (T := T) (d := d) (v := v) (β := β) t)))
  let BI : Finset (Equiv.Perm (Fin N)) := (range T).biUnion (fun t =>
    (univ : Finset (Element d)).biUnion (fun A =>
      ((univ : Finset (Finset (Fin v))).filter (fun Y => Y.card ≤ r)).biUnion
        (fun Y => avoid (GG (T := T) (d := d) (v := v) (β := β) t A Y) (τ t))))
  have hbad : univ \ goodSet (T := T) (d := d) (v := v) (β := β) r τ ⊆ BE ∪ BI := by
    intro π hπ
    simp only [mem_sdiff, mem_univ, true_and, mem_goodSet] at hπ
    rcases not_and_or.mp hπ with h1 | h1
    · apply mem_union_left
      simp only [goodE, not_forall, not_le] at h1
      obtain ⟨t, ht, i, hi, hlev⟩ := h1
      simp only [BE, mem_biUnion, mem_range, mem_filter, mem_univ, true_and]
      exact ⟨t, ht, i, hi, by simp [HH, hlev]⟩
    · apply mem_union_right
      simp only [goodI, not_forall, not_exists, not_and] at h1
      obtain ⟨t, ht, A, Y, hY, hav⟩ := h1
      simp only [BI, mem_biUnion, mem_range, mem_univ, true_and, mem_filter]
      refine ⟨t, ht, A, Y, hY, ?_⟩
      simp only [avoid, mem_filter, mem_univ, true_and]
      exact fun i hi => hav i hi
  -- the E part
  have hBE : 20 * BE.card ≤ N.factorial := by
    have h1 : BE.card * N ≤ ∑ t ∈ range T, τ t * (HH (T := T) (d := d) (v := v) (β := β) t).card *
        N.factorial := by
      calc BE.card * N ≤ (∑ t ∈ range T, ∑ i ∈ univ.filter (fun i : Fin N => i.val < τ t),
            (univ.filter (fun π : Equiv.Perm (Fin N) =>
              π i ∈ HH (T := T) (d := d) (v := v) (β := β) t)).card) * N := by
            apply Nat.mul_le_mul_right
            refine card_biUnion_le.trans (sum_le_sum fun t _ => card_biUnion_le)
        _ = ∑ t ∈ range T, ∑ i ∈ univ.filter (fun i : Fin N => i.val < τ t),
            (HH (T := T) (d := d) (v := v) (β := β) t).card * N.factorial := by
            rw [sum_mul]
            refine sum_congr rfl fun t _ => ?_
            rw [sum_mul]
            exact sum_congr rfl fun i _ => perm_card_mem i _
        _ ≤ ∑ t ∈ range T, τ t * (HH (T := T) (d := d) (v := v) (β := β) t).card *
              N.factorial := by
            apply sum_le_sum
            intro t _
            rw [sum_const, smul_eq_mul, Fin.card_filter_val_lt, mul_assoc]
            exact Nat.mul_le_mul_right _ (min_le_right _ _)
    have h2 : 20 * (BE.card * N) ≤ N * N.factorial := by
      calc 20 * (BE.card * N) ≤ 20 * ∑ t ∈ range T, τ t *
            (HH (T := T) (d := d) (v := v) (β := β) t).card * N.factorial :=
            Nat.mul_le_mul_left _ h1
        _ = (20 * ∑ t ∈ range T, τ t * (HH (T := T) (d := d) (v := v) (β := β) t).card) *
              N.factorial := by rw [← sum_mul, mul_assoc]
        _ ≤ N * N.factorial := Nat.mul_le_mul_right _ hE
    have : 20 * BE.card * N ≤ N.factorial * N := by linarith
    exact Nat.le_of_mul_le_mul_right this hN
  -- the I part
  have hBI : (BI.card : ℝ) ≤ N.factorial / 32 := by
    have hexpM : Real.exp (-(M : ℝ)) * 2 ^ M ≤ 1 := by
      have h2 : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp 1; linarith
      have h3 : (2 : ℝ) ^ M ≤ Real.exp M := by
        calc (2 : ℝ) ^ M ≤ Real.exp 1 ^ M := pow_le_pow_left₀ (by norm_num) h2 M
          _ = Real.exp M := by rw [← Real.exp_nat_mul, mul_one]
      calc Real.exp (-(M : ℝ)) * 2 ^ M ≤ Real.exp (-(M : ℝ)) * Real.exp M :=
            mul_le_mul_of_nonneg_left h3 (Real.exp_pos _).le
        _ = 1 := by rw [← Real.exp_add]; simp
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    have hone : ∀ t, t < T → ∀ (A : Element d) (Y : Finset (Fin v)), Y.card ≤ r →
        ((avoid (GG (T := T) (d := d) (v := v) (β := β) t A Y) (τ t)).card : ℝ) ≤
          N.factorial * Real.exp (-(M : ℝ)) := by
      intro t ht A Y hY
      refine (avoid_bound_exp _ (τ t) (hτN t ht) hN).trans ?_
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      have hc : (M : ℝ) * N ≤ (GG (T := T) (d := d) (v := v) (β := β) t A Y).card * τ t := by
        exact_mod_cast hI t ht A Y hY
      rw [neg_mul, neg_div, neg_le_neg_iff, le_div_iff₀ hNr]
      linarith
    have hcnt : ((range T).card * (univ : Finset (Element d)).card *
        ((univ : Finset (Finset (Fin v))).filter (fun Y => Y.card ≤ r)).card : ℝ) ≤
        T * 2 ^ d * 2 ^ v := by
      have a1 : (univ : Finset (Element d)).card ≤ 2 ^ d := by
        rw [card_univ]; exact card_element_le
      have a2 : ((univ : Finset (Finset (Fin v))).filter (fun Y => Y.card ≤ r)).card ≤ 2 ^ v := by
        refine (card_filter_le _ _).trans ?_
        rw [card_univ, Fintype.card_finset, Fintype.card_fin]
      rw [card_range]
      have : (T * (univ : Finset (Element d)).card *
          ((univ : Finset (Finset (Fin v))).filter (fun Y => Y.card ≤ r)).card) ≤
          T * 2 ^ d * 2 ^ v := Nat.mul_le_mul (Nat.mul_le_mul_left _ a1) a2
      exact_mod_cast this
    have hsum : (BI.card : ℝ) ≤ (range T).card * (univ : Finset (Element d)).card *
        ((univ : Finset (Finset (Fin v))).filter (fun Y => Y.card ≤ r)).card *
        (N.factorial * Real.exp (-(M : ℝ))) := by
      have : BI.card ≤ ∑ t ∈ range T, ∑ A : Element d,
          ∑ Y ∈ (univ : Finset (Finset (Fin v))).filter (fun Y => Y.card ≤ r),
            (avoid (GG (T := T) (d := d) (v := v) (β := β) t A Y) (τ t)).card := by
        refine card_biUnion_le.trans (sum_le_sum fun t _ => ?_)
        exact card_biUnion_le.trans (sum_le_sum fun A _ => card_biUnion_le)
      calc (BI.card : ℝ) ≤ ∑ t ∈ range T, ∑ A : Element d,
          ∑ Y ∈ (univ : Finset (Finset (Fin v))).filter (fun Y => Y.card ≤ r),
            ((avoid (GG (T := T) (d := d) (v := v) (β := β) t A Y) (τ t)).card : ℝ) := by
            exact_mod_cast this
        _ ≤ ∑ _t ∈ range T, ∑ _A : Element d,
          ∑ _Y ∈ (univ : Finset (Finset (Fin v))).filter (fun Y => Y.card ≤ r),
            (N.factorial * Real.exp (-(M : ℝ))) := by
            apply sum_le_sum; intro t ht
            apply sum_le_sum; intro A _
            apply sum_le_sum; intro Y hY
            simp only [mem_filter, mem_univ, true_and] at hY
            exact hone t (mem_range.mp ht) A Y hY
        _ = _ := by simp only [sum_const, nsmul_eq_mul]; ring
    have hc32 : (32 : ℝ) * (T * 2 ^ d * 2 ^ v) ≤ 2 ^ M := by exact_mod_cast hcount
    have hE0 : 0 ≤ Real.exp (-(M : ℝ)) := (Real.exp_pos _).le
    have hF0 : (0 : ℝ) ≤ N.factorial := by positivity
    calc (BI.card : ℝ) ≤ T * 2 ^ d * 2 ^ v * (N.factorial * Real.exp (-(M : ℝ))) :=
          hsum.trans (mul_le_mul_of_nonneg_right hcnt (by positivity))
      _ ≤ (2 ^ M / 32) * (N.factorial * Real.exp (-(M : ℝ))) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          linarith
      _ = N.factorial * (Real.exp (-(M : ℝ)) * 2 ^ M) / 32 := by ring
      _ ≤ N.factorial * 1 / 32 := by
          apply div_le_div_of_nonneg_right _ (by norm_num)
          exact mul_le_mul_of_nonneg_left hexpM hF0
      _ = N.factorial / 32 := by ring
  -- combine
  have hsplit := card_sdiff_add_card_inter (s := (univ : Finset (Equiv.Perm (Fin N))))
    (t := goodSet (T := T) (d := d) (v := v) (β := β) r τ)
  rw [univ_inter, card_univ, Fintype.card_perm, Fintype.card_fin] at hsplit
  have hbc : (univ \ goodSet (T := T) (d := d) (v := v) (β := β) r τ).card ≤ BE.card + BI.card :=
    (card_le_card hbad).trans (card_union_le _ _)
  have hr1 : ((univ \ goodSet (T := T) (d := d) (v := v) (β := β) r τ).card : ℝ) +
      (goodSet (T := T) (d := d) (v := v) (β := β) r τ).card = N.factorial := by
    exact_mod_cast hsplit
  have hr2 : ((univ \ goodSet (T := T) (d := d) (v := v) (β := β) r τ).card : ℝ) ≤
      BE.card + BI.card := by exact_mod_cast hbc
  have hr3 : (20 : ℝ) * BE.card ≤ N.factorial := by exact_mod_cast hBE
  have hF0 : (0 : ℝ) ≤ N.factorial := by positivity
  linarith

end Good

end RandOnlineSetCoverSqrt.Dev.T14D
end

section
set_option autoImplicit false

open scoped ENNReal

namespace RandOnlineSetCoverSqrt.Dev.T14
open RandOnlineSetCoverSqrt.LowerBound RandOnlineSetCover.InfoLB
open RandOnlineSetCoverSqrt.LowerBound.Supplement
open RandOnlineSetCoverSqrt.Dev.T14A RandOnlineSetCoverSqrt.Dev.T14B RandOnlineSetCoverSqrt.Dev.T14C
open RandOnlineSetCoverSqrt.Dev.T14D
open Finset

/-! ### Parameters (all functions of `x`; core size `d = x²`) -/

def vv (x : ℕ) : ℕ := 32 * x ^ 3
def gg (x : ℕ) : ℕ := 2 * x ^ 2
def rr (x : ℕ) : ℕ := x ^ 2 / 32
def bb (x t : ℕ) : ℕ := (4 * x - t) * gg x
def LL (x t : ℕ) : ℕ := Nat.choose (vv x) (bb x t)
def MM (x : ℕ) : ℕ := vv x + x ^ 2 + 4 * x + 5
def ss (x : ℕ) : ℕ := 4 ^ rr x * MM x

noncomputable def NX (x : ℕ) : ℕ := NN (4 * x) (x ^ 2) (vv x) (bb x)

noncomputable def tau (x t : ℕ) : ℕ := ss x * NX x / LL x t + 1

section Numerics

variable {x : ℕ}

theorem bb_le (t : ℕ) : bb x t ≤ 8 * x ^ 3 := by
  unfold bb gg
  calc (4 * x - t) * (2 * x ^ 2) ≤ (4 * x) * (2 * x ^ 2) :=
        Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    _ = 8 * x ^ 3 := by ring

theorem three_bb (hx : 1 ≤ x) (t : ℕ) : 3 * bb x t + 2 ≤ vv x := by
  have := bb_le (x := x) t
  have h3 : 1 ≤ x ^ 3 := Nat.one_le_pow _ _ hx
  unfold vv; omega

theorem bb_succ (t : ℕ) (ht : t < 4 * x) : bb x t = bb x (t + 1) + gg x := by
  unfold bb
  have : 4 * x - t = (4 * x - (t + 1)) + 1 := by omega
  rw [this]; ring

theorem bb_anti (t t' : ℕ) (h : t ≤ t') : bb x t' ≤ bb x t := by
  unfold bb
  exact Nat.mul_le_mul_right _ (Nat.sub_le_sub_left h _)

theorem LL_anti (hx : 1 ≤ x) (t t' : ℕ) (h : t ≤ t') : LL x t' ≤ LL x t :=
  choose_mono_of _ _ _ (bb_anti t t' h) (three_bb hx t)

theorem LL_succ (hx : 1 ≤ x) (t : ℕ) (ht : t < 4 * x) : LL x (t + 1) * 2 ^ gg x ≤ LL x t := by
  unfold LL
  rw [bb_succ t ht]
  apply choose_double
  rw [← bb_succ t ht]; exact three_bb hx t

theorem LL_pos (hx : 1 ≤ x) (t : ℕ) : 0 < LL x t := by
  unfold LL
  apply Nat.choose_pos
  have := three_bb hx t; omega

theorem LL_ge (hx : 1 ≤ x) (t : ℕ) (ht : t < 4 * x) : 2 ^ gg x ≤ LL x t := by
  have h1 := choose_double (vv x) 0 (bb x t) (by simpa using three_bb hx t)
  rw [Nat.choose_zero_right, one_mul, zero_add] at h1
  have h2 : gg x ≤ bb x t := by
    unfold bb
    have : 1 ≤ 4 * x - t := by omega
    calc gg x = 1 * gg x := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ this
  exact (Nat.pow_le_pow_right (by norm_num) h2).trans h1

theorem key_E (hx : 64 ≤ x) : 40 * ss x * (4 * x) ^ 2 * 2 ^ (x ^ 2) ≤ 2 ^ gg x := by
  have hx1 : 1 ≤ x := by omega
  have hx2 : x ^ 2 ≤ x ^ 3 := Nat.pow_le_pow_right hx1 (by norm_num)
  have hx1' : x ≤ x ^ 3 := by
    calc x = x ^ 1 := (pow_one x).symm
      _ ≤ x ^ 3 := Nat.pow_le_pow_right hx1 (by norm_num)
  have h13 : 1 ≤ x ^ 3 := Nat.one_le_pow _ _ hx1
  have hM : MM x ≤ 42 * x ^ 3 := by unfold MM vv; omega
  have hP : 40 * MM x * (4 * x) ^ 2 ≤ 2 ^ 15 * 2 ^ (5 * x) := by
    have hx5 : x ^ 5 ≤ 2 ^ (5 * x) := by
      rw [mul_comm, pow_mul]
      exact Nat.pow_le_pow_left Nat.lt_two_pow_self.le 5
    calc 40 * MM x * (4 * x) ^ 2 ≤ 40 * (42 * x ^ 3) * (4 * x) ^ 2 := by
          apply Nat.mul_le_mul_right; exact Nat.mul_le_mul_left _ hM
      _ = 26880 * x ^ 5 := by ring
      _ ≤ 2 ^ 15 * x ^ 5 := Nat.mul_le_mul_right _ (by norm_num)
      _ ≤ 2 ^ 15 * 2 ^ (5 * x) := Nat.mul_le_mul_left _ hx5
  have h4 : 4 ^ rr x = 2 ^ (2 * rr x) := by rw [pow_mul]; norm_num
  have hy : 64 * x ≤ x ^ 2 := by rw [sq]; exact Nat.mul_le_mul_right _ hx
  have hr32 : 32 * rr x ≤ x ^ 2 := by unfold rr; omega
  have hexp : 15 + 5 * x + 2 * rr x + x ^ 2 ≤ gg x := by unfold gg; omega
  calc 40 * ss x * (4 * x) ^ 2 * 2 ^ (x ^ 2) =
        (40 * MM x * (4 * x) ^ 2) * 2 ^ (2 * rr x) * 2 ^ (x ^ 2) := by
        unfold ss; rw [h4]; ring
    _ ≤ (2 ^ 15 * 2 ^ (5 * x)) * 2 ^ (2 * rr x) * 2 ^ (x ^ 2) := by
        apply Nat.mul_le_mul_right; exact Nat.mul_le_mul_right _ hP
    _ = 2 ^ (15 + 5 * x + 2 * rr x + x ^ 2) := by rw [pow_add, pow_add, pow_add]
    _ ≤ 2 ^ gg x := Nat.pow_le_pow_right (by norm_num) hexp

theorem key_I (x : ℕ) : 32 * (4 * x * 2 ^ (x ^ 2) * 2 ^ vv x) ≤ 2 ^ MM x := by
  have h1 : 4 * x ≤ 2 ^ (4 * x) := Nat.lt_two_pow_self.le
  calc 32 * (4 * x * 2 ^ (x ^ 2) * 2 ^ vv x) ≤ 2 ^ 5 * (2 ^ (4 * x) * 2 ^ (x ^ 2) * 2 ^ vv x) := by
        apply Nat.mul_le_mul (by norm_num)
        exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h1)
    _ = 2 ^ MM x := by unfold MM; rw [← pow_add, ← pow_add, ← pow_add]; congr 1; ring

theorem ss_pos (x : ℕ) : 1 ≤ ss x := by
  unfold ss MM
  exact Nat.succ_le_of_lt (by positivity)

theorem two_ss_le (hx : 64 ≤ x) : 2 * ss x ≤ 2 ^ gg x := by
  have := key_E hx
  have h1 : 1 ≤ (4 * x) ^ 2 * 2 ^ (x ^ 2) := Nat.succ_le_of_lt (by positivity)
  calc 2 * ss x ≤ 40 * ss x * ((4 * x) ^ 2 * 2 ^ (x ^ 2)) := by
        calc 2 * ss x ≤ 40 * ss x := by omega
          _ = 40 * ss x * 1 := by ring
          _ ≤ _ := Nat.mul_le_mul_left _ h1
    _ = 40 * ss x * (4 * x) ^ 2 * 2 ^ (x ^ 2) := by ring
    _ ≤ _ := this

theorem avoid_cond (hx : 64 ≤ x) (t : ℕ) : 4 * bb x t ≤ 3 * (vv x - rr x + 1) := by
  have h1 := bb_le (x := x) t
  have hr : rr x ≤ x ^ 3 := by
    have : x ^ 2 ≤ x ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
    unfold rr; omega
  unfold vv; omega

theorem rr_le_vv (hx : 64 ≤ x) : rr x ≤ vv x := by
  have : x ^ 2 ≤ x ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  unfold rr vv; omega

theorem bb_inj (hx : 1 ≤ x) (t t' : ℕ) (ht : t < 4 * x) (ht' : t' < 4 * x)
    (h : bb x t = bb x t') : t = t' := by
  unfold bb at h
  have hg : 0 < gg x := by unfold gg; positivity
  have := Nat.eq_of_mul_eq_mul_right hg h
  omega

/-! #### Facts about `N` and `τ` -/

theorem LL_le_NX (hx : 1 ≤ x) (t : ℕ) (ht : t < 4 * x) : LL x t ≤ NX x :=
  choose_le_NN (T := 4 * x) (d := x ^ 2) (v := vv x) (β := bb x) t ht (by positivity)

theorem NX_ge (hx : 64 ≤ x) : 2 ≤ NX x := by
  have h1 := LL_le_NX (x := x) (by omega) 0 (by omega)
  have h2 := LL_ge (x := x) (by omega) 0 (by omega)
  have h3 : 2 ≤ 2 ^ gg x := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ gg x := Nat.pow_le_pow_right (by norm_num) (by
          unfold gg; have : 1 ≤ x ^ 2 := Nat.one_le_pow _ _ (by omega)
          omega)
  omega

theorem tau_le (hx : 64 ≤ x) (t : ℕ) (ht : t < 4 * x) : tau x t ≤ NX x := by
  unfold tau
  have hL : 2 * ss x ≤ LL x t := (two_ss_le hx).trans (LL_ge (by omega) t ht)
  have hs := ss_pos x
  have h1 : ss x * NX x / LL x t ≤ ss x * NX x / (2 * ss x) :=
    Nat.div_le_div_left hL (by omega)
  have h2 : ss x * NX x / (2 * ss x) = NX x / 2 := by
    rw [mul_comm 2 (ss x), Nat.mul_div_mul_left _ _ (by omega)]
  have := NX_ge hx
  omega

theorem tau_mono (hx : 1 ≤ x) (t : ℕ) : tau x t ≤ tau x (t + 1) := by
  unfold tau
  have := Nat.div_le_div_left (a := ss x * NX x) (LL_anti hx t (t + 1) (by omega))
    (LL_pos hx (t + 1))
  omega

theorem tau_mul (hx : 1 ≤ x) (t : ℕ) : ss x * NX x ≤ tau x t * LL x t := by
  unfold tau
  have := Nat.lt_div_mul_add (a := ss x * NX x) (LL_pos hx t)
  rw [add_mul, one_mul]; omega

theorem hE_bound (hx : 64 ≤ x) :
    20 * ∑ t ∈ range (4 * x),
      tau x t * (HH (T := 4 * x) (d := x ^ 2) (v := vv x) (β := bb x) t).card ≤ NX x := by
  have hx1 : 1 ≤ x := by omega
  have hone : ∀ t ∈ range (4 * x), 2 ^ gg x *
      (tau x t * (HH (T := 4 * x) (d := x ^ 2) (v := vv x) (β := bb x) t).card) ≤
      4 * x * 2 ^ (x ^ 2) * (2 * (ss x * NX x)) := by
    intro t ht
    rw [mem_range] at ht
    have hH := card_HH (T := 4 * x) (d := x ^ 2) (v := vv x) (β := bb x) t (LL x (t + 1))
      (fun t' h1 _ => LL_anti hx1 (t + 1) t' (by omega))
    have hs := LL_succ hx1 t ht
    have hτ : tau x t * LL x t ≤ 2 * (ss x * NX x) := by
      unfold tau
      rw [add_mul, one_mul]
      have a1 := Nat.div_mul_le_self (ss x * NX x) (LL x t)
      have a2 := LL_le_NX hx1 t ht
      have a3 : NX x ≤ ss x * NX x := Nat.le_mul_of_pos_left _ (ss_pos x)
      omega
    calc 2 ^ gg x * (tau x t * (HH (T := 4 * x) (d := x ^ 2) (v := vv x) (β := bb x) t).card)
        ≤ 2 ^ gg x * (tau x t * (4 * x * 2 ^ (x ^ 2) * LL x (t + 1))) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hH)
      _ = 4 * x * 2 ^ (x ^ 2) * (tau x t * (LL x (t + 1) * 2 ^ gg x)) := by ring
      _ ≤ 4 * x * 2 ^ (x ^ 2) * (tau x t * LL x t) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hs)
      _ ≤ 4 * x * 2 ^ (x ^ 2) * (2 * (ss x * NX x)) := Nat.mul_le_mul_left _ hτ
  have hsum : 2 ^ gg x * ∑ t ∈ range (4 * x),
      tau x t * (HH (T := 4 * x) (d := x ^ 2) (v := vv x) (β := bb x) t).card ≤
      4 * x * (4 * x * 2 ^ (x ^ 2) * (2 * (ss x * NX x))) := by
    rw [mul_sum]
    calc _ ≤ ∑ _t ∈ range (4 * x), 4 * x * 2 ^ (x ^ 2) * (2 * (ss x * NX x)) := sum_le_sum hone
      _ = _ := by rw [sum_const, card_range, smul_eq_mul]
  have hk := key_E hx
  have hpos : 0 < 2 ^ gg x := by positivity
  have : 2 ^ gg x * (20 * ∑ t ∈ range (4 * x),
      tau x t * (HH (T := 4 * x) (d := x ^ 2) (v := vv x) (β := bb x) t).card) ≤
      2 ^ gg x * NX x := by
    calc 2 ^ gg x * (20 * ∑ t ∈ range (4 * x),
        tau x t * (HH (T := 4 * x) (d := x ^ 2) (v := vv x) (β := bb x) t).card)
        = 20 * (2 ^ gg x * ∑ t ∈ range (4 * x),
          tau x t * (HH (T := 4 * x) (d := x ^ 2) (v := vv x) (β := bb x) t).card) := by ring
      _ ≤ 20 * (4 * x * (4 * x * 2 ^ (x ^ 2) * (2 * (ss x * NX x)))) := Nat.mul_le_mul_left _ hsum
      _ = (40 * ss x * (4 * x) ^ 2 * 2 ^ (x ^ 2)) * NX x := by ring
      _ ≤ 2 ^ gg x * NX x := Nat.mul_le_mul_right _ hk
  exact Nat.le_of_mul_le_mul_left this hpos

theorem hI_bound (hx : 64 ≤ x) (t : ℕ) (ht : t < 4 * x) (A : Element (x ^ 2))
    (Y : Finset (Fin (vv x))) (hY : Y.card ≤ rr x) :
    MM x * NX x ≤ (GG (T := 4 * x) (d := x ^ 2) (v := vv x) (β := bb x) t A Y).card * tau x t := by
  have hx1 : 1 ≤ x := by omega
  have hG := card_GG (T := 4 * x) (d := x ^ 2) (v := vv x) (β := bb x) (rr x) t ht A Y hY
    (rr_le_vv hx) (avoid_cond hx t)
  have h1 := tau_mul hx1 t
  have hp : 0 < 4 ^ rr x := by positivity
  have : 4 ^ rr x * (MM x * NX x) ≤
      4 ^ rr x * ((GG (T := 4 * x) (d := x ^ 2) (v := vv x) (β := bb x) t A Y).card * tau x t) := by
    calc 4 ^ rr x * (MM x * NX x) = ss x * NX x := by unfold ss; ring
      _ ≤ tau x t * LL x t := h1
      _ ≤ tau x t * (4 ^ rr x * (GG (T := 4 * x) (d := x ^ 2) (v := vv x) (β := bb x) t A Y).card) :=
          Nat.mul_le_mul_left _ hG
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_left this hp

end Numerics

/-! ### Union expansion of the embedded family -/

theorem ue_C0' {d v m k q r : ℕ} (h : 2 * d + v ≤ m) (C₀ : Family d)
    (hue : UnionExpanding k q r C₀) (hrm : r ≤ m) : UnionExpanding k q r (C0' h C₀) := by
  obtain ⟨hk1, hkr, -, hq2, hcard, hexp⟩ := hue
  refine ⟨hk1, hkr, hrm, hq2, ?_, ?_⟩
  · intro V hV
    obtain ⟨W, hW, rfl⟩ := (mem_C0' h C₀ V).mp hV
    rw [card_map]; exact hcard W hW
  · intro Q hQ hQc
    have hpc : (pull h Q).card = Q.card := by
      apply Finset.card_nbij (fun W => W.map (eC h))
      · intro W hW; exact (mem_pull h Q W).mp hW
      · intro a _ b _ hab; exact Finset.map_injective (eC h) hab
      · intro V hV
        obtain ⟨W, _, rfl⟩ := (mem_C0' h C₀ V).mp (hQ hV)
        exact ⟨W, (mem_pull h Q W).mpr hV, rfl⟩
    have h1 := hexp (pull h Q) (pull_sub h C₀ Q hQ) (by rw [hpc, hQc])
    refine lt_of_lt_of_le h1 ?_
    apply card_le_card_of_injOn (eC h)
    · intro a ha
      rw [mem_coe, mem_biUnion] at ha ⊢
      obtain ⟨W, hW, haW⟩ := ha
      exact ⟨W.map (eC h), (mem_pull h Q W).mp hW, mem_map_of_mem _ haW⟩
    · intro a _ b _ hab; exact (eC h).injective hab

/-! ### Yao's principle for the random-order cost -/

theorem yao_ro {Ω : Type*} [Fintype Ω] [Nonempty Ω] {m N : ℕ} (I : Ω → Instance m N) (L : ℝ)
    (R : RandAlg m N)
    (hA : ∀ A : DetAlg m N, L ≤ (∑ π : Equiv.Perm (Fin N),
      ∑ ω, (Fintype.card Ω : ℝ)⁻¹ * (cost A (reorder (I ω) π) : ℝ)) / (N.factorial : ℝ)) :
    ∃ ω, L ≤ randomOrderExpectedCost R (I ω) := by
  by_contra hcon
  push Not at hcon
  set w : ℝ := (Fintype.card Ω : ℝ)⁻¹
  have hw : 0 < w := by positivity
  have hsum : ∑ _ω : Ω, w * L = L := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
      mul_inv_cancel₀ (by positivity), one_mul]
  have hlt : ∑ ω, w * randomOrderExpectedCost R (I ω) < ∑ _ω : Ω, w * L :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
      (fun ω _ => mul_lt_mul_of_pos_left (hcon ω) hw)
  have hswap : ∑ ω, w * randomOrderExpectedCost R (I ω) =
      ∑ A, (R A).toReal * ((∑ π : Equiv.Perm (Fin N),
        ∑ ω, w * (cost A (reorder (I ω) π) : ℝ)) / (N.factorial : ℝ)) := by
    unfold randomOrderExpectedCost expectedCost
    simp only [Finset.sum_div, Finset.mul_sum]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun π _ => Finset.sum_comm)]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun A _ => Finset.sum_congr rfl fun π _ =>
      Finset.sum_congr rfl fun ω _ => ?_
    ring
  have hge : L ≤ ∑ A, (R A).toReal * ((∑ π : Equiv.Perm (Fin N),
      ∑ ω, w * (cost A (reorder (I ω) π) : ℝ)) / (N.factorial : ℝ)) := by
    calc L = ∑ A, (R A).toReal * L := by rw [← Finset.sum_mul, pmf_sum_toReal, one_mul]
      _ ≤ _ := Finset.sum_le_sum fun A _ =>
          mul_le_mul_of_nonneg_left (hA A) ENNReal.toReal_nonneg
  linarith

/-! ### The average over orders, for one deterministic algorithm -/

theorem avg_bound {N : ℕ} (F : Equiv.Perm (Fin N) → ℝ)
    (good : Finset (Equiv.Perm (Fin N))) (L : ℝ) (hL : 0 ≤ L)
    (hF0 : ∀ π, 0 ≤ F π) (hFg : ∀ π ∈ good, L ≤ F π)
    (hgood : (9 / 10 : ℝ) * N.factorial ≤ good.card) :
    (9 / 10 : ℝ) * L ≤ (∑ π, F π) / (N.factorial : ℝ) := by
  have hNf : (0 : ℝ) < N.factorial := by exact_mod_cast Nat.factorial_pos N
  rw [le_div_iff₀ hNf]
  calc 9 / 10 * L * N.factorial = L * (9 / 10 * N.factorial) := by ring
    _ ≤ L * good.card := mul_le_mul_of_nonneg_left hgood hL
    _ = ∑ _π ∈ good, L := by rw [sum_const, nsmul_eq_mul]; ring
    _ ≤ ∑ π ∈ good, F π := sum_le_sum hFg
    _ ≤ ∑ π, F π := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun π _ _ => hF0 π)

/-! ### Constants -/

theorem final_ineq (m x : ℕ) (hx : 64 ≤ x) (hm : (m : ℝ) ^ ((1 : ℝ) / 3) ≤ 4 * (x + 1))
    (opt : ℕ) (hopt : opt ≤ x) :
    1 / 1000 * (m : ℝ) ^ ((1 : ℝ) / 3) * (opt : ℝ) ≤
      9 / 10 * ((1 - Real.exp (-(x : ℝ) / 4)) * (rr x : ℝ)) := by
  have hxr : (64 : ℝ) ≤ x := by exact_mod_cast hx
  have hexp : Real.exp (-(x : ℝ) / 4) ≤ 1 / 2 := by
    have h1 : Real.exp (-(x : ℝ) / 4) ≤ Real.exp (-2) := Real.exp_le_exp.mpr (by linarith)
    have h2 : 2 + 1 ≤ Real.exp 2 := Real.add_one_le_exp 2
    have h3 : Real.exp (-2) * Real.exp 2 = 1 := by rw [← Real.exp_add]; simp
    have h4 : 0 < Real.exp (-2) := Real.exp_pos _
    nlinarith
  have hr : (x : ℝ) ^ 2 ≤ 64 * (rr x : ℝ) := by
    have hy : 64 * x ≤ x ^ 2 := by rw [sq]; exact Nat.mul_le_mul_right _ hx
    have : x ^ 2 ≤ 64 * rr x := by unfold rr; omega
    exact_mod_cast this
  have ho : (opt : ℝ) ≤ x := by exact_mod_cast hopt
  have ho0 : (0 : ℝ) ≤ opt := Nat.cast_nonneg _
  have hm0 : (0 : ℝ) ≤ (m : ℝ) ^ ((1 : ℝ) / 3) := by positivity
  have hr0 : (0 : ℝ) ≤ rr x := Nat.cast_nonneg _
  have h1 : (m : ℝ) ^ ((1 : ℝ) / 3) * opt ≤ 4 * (x + 1) * x :=
    mul_le_mul hm ho ho0 (by positivity)
  have h2 : (1 / 2 : ℝ) * rr x ≤ (1 - Real.exp (-(x : ℝ) / 4)) * rr x :=
    mul_le_mul_of_nonneg_right (by linarith) hr0
  nlinarith

end RandOnlineSetCoverSqrt.Dev.T14

namespace RandOnlineSetCoverSqrt.LowerBound.Supplement
open RandOnlineSetCoverSqrt.LowerBound RandOnlineSetCover.InfoLB
open RandOnlineSetCoverSqrt.Dev.T14A RandOnlineSetCoverSqrt.Dev.T14C RandOnlineSetCoverSqrt.Dev.T14D
open RandOnlineSetCoverSqrt.Dev.T14 in
theorem chk_theorem_1_4 :
    ∃ c : ℝ, 0 < c ∧ ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∃ N : ℕ, 0 < N ∧
      ∀ R : RandOnlineSetCover.InfoLB.RandAlg m N,
      ∃ I : RandOnlineSetCover.InfoLB.Instance m N,
        DistinctRequests I ∧
        1 ≤ RandOnlineSetCover.InfoLB.Opt I ∧
        c * (m : ℝ) ^ ((1 : ℝ) / 3) * (RandOnlineSetCover.InfoLB.Opt I : ℝ) ≤
          randomOrderExpectedCost R I := by
  obtain ⟨m₁, hm₁⟩ := lemma_3_5
  set X₀ := max 64 m₁
  refine ⟨1 / 1000, by norm_num, 64 * X₀ ^ 3, ?_⟩
  intro m hm
  -- the scale `x`: the largest with `64 x³ ≤ m`
  set x := Nat.findGreatest (fun y => 64 * y ^ 3 ≤ m) m with hxdef
  have hX₀m : X₀ ≤ m := by
    have : X₀ ≤ X₀ ^ 3 := by
      calc X₀ = X₀ ^ 1 := (pow_one _).symm
        _ ≤ X₀ ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
    omega
  have hxX : X₀ ≤ x := Nat.le_findGreatest (P := fun y => 64 * y ^ 3 ≤ m) hX₀m hm
  have hx64 : 64 ≤ x := le_trans (le_max_left _ _) hxX
  have hx1 : 1 ≤ x := by omega
  have hxm : 64 * x ^ 3 ≤ m := Nat.findGreatest_spec (P := fun y => 64 * y ^ 3 ≤ m) hX₀m hm
  have hxm' : m < 64 * (x + 1) ^ 3 := by
    by_contra hcon
    push Not at hcon
    have hle : x + 1 ≤ m := by
      have : x + 1 ≤ (x + 1) ^ 3 := by
        calc x + 1 = (x + 1) ^ 1 := (pow_one _).symm
          _ ≤ (x + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
      omega
    exact Nat.findGreatest_is_greatest (P := fun y => 64 * y ^ 3 ≤ m) (Nat.lt_succ_self x) hle hcon
  have hreg : 2 * x ^ 2 + vv x ≤ m := by
    have : x ^ 2 ≤ x ^ 3 := Nat.pow_le_pow_right hx1 (by norm_num)
    unfold vv; omega
  -- the union-expanding family at `d = x²`
  have hd : m₁ ≤ x ^ 2 := by
    have : x ≤ x ^ 2 := by
      calc x = x ^ 1 := (pow_one _).symm
        _ ≤ x ^ 2 := Nat.pow_le_pow_right hx1 (by norm_num)
    have : m₁ ≤ x := le_trans (le_max_right _ _) hxX
    omega
  obtain ⟨C₀, hcard, hexp⟩ := hm₁ (x ^ 2) hd
  have hk : kParam (x ^ 2) = x := by unfold kParam; push_cast; simp
  have hq : qParam (x ^ 2) = x := by unfold qParam; push_cast; simp
  have hrp : rParam (x ^ 2) = rr x := rfl
  rw [hk, hq, hrp] at hexp
  have hC : C₀.card = 2 ^ (4 * x) := by rw [hcard]; unfold familySize; rw [hq]
  obtain ⟨-, hkr, -, -, hCk, -⟩ := id hexp
  have hne : ∀ W ∈ C₀, W.Nonempty := fun W hW => Finset.card_pos.mp (by rw [hCk W hW]; omega)
  have hr1 : 1 ≤ rr x := le_trans hx1 hkr
  have hrm : rr x ≤ m := by
    have := Nat.div_le_self (x ^ 2) 32
    have : x ^ 2 ≤ x ^ 3 := Nat.pow_le_pow_right hx1 (by norm_num)
    unfold rr; omega
  have hexp' := ue_C0' hreg C₀ hexp hrm
  have hC' : (C0' hreg C₀).card = 2 ^ (4 * x) := by rw [card_C0', hC]
  have hN : 0 < NX x := by have := NX_ge hx64; omega
  refine ⟨NX x, hN, ?_⟩
  intro R
  -- for each deterministic algorithm, the average over orders
  have hβ : ∀ t t', t < 4 * x → t' < 4 * x → bb x t = bb x t' → t = t' :=
    fun t t' ht ht' h => bb_inj hx1 t t' ht ht' h
  have hgood := good_card (T := 4 * x) (d := x ^ 2) (v := vv x) (β := bb x) (rr x) (MM x)
    (tau x) hN (fun t ht => tau_le hx64 t ht) (hE_bound hx64)
    (fun t ht A Y hY => hI_bound hx64 t ht A Y hY) (key_I x)
  set L₀ : ℝ := (1 - Real.exp (-(x : ℝ) / 4)) * (rr x : ℝ)
  have hL₀ : 0 ≤ L₀ := by
    apply mul_nonneg _ (Nat.cast_nonneg _)
    have : Real.exp (-(x : ℝ) / 4) ≤ 1 := Real.exp_le_one_iff.mpr (by
      have : (0 : ℝ) ≤ x := Nat.cast_nonneg _
      linarith)
    linarith
  obtain ⟨ω, hω⟩ := yao_ro (fun ω : Omega (4 * x) => inst (β := bb x) hreg (rr x) C₀ ω)
    (9 / 10 * L₀) R (fun A => by
      apply avg_bound
        (fun π => ∑ ω : Omega (4 * x), (Fintype.card (Omega (4 * x)) : ℝ)⁻¹ *
          (cost A (reorder (inst (β := bb x) hreg (rr x) C₀ ω) π) : ℝ))
        (goodSet (T := 4 * x) (d := x ^ 2) (v := vv x) (β := bb x) (rr x) (tau x)) L₀ hL₀
      · intro π
        exact Finset.sum_nonneg (fun ω _ => mul_nonneg (by positivity) (Nat.cast_nonneg _))
      · intro π hπ
        rw [mem_goodSet] at hπ
        obtain ⟨hπE, hπI⟩ := hπ
        set X := Xp (β := bb x) hreg (rr x) C₀ (tau x) A π
        have hXupd : ∀ ω (t : Fin (4 * x)) (j : Fin (Nn (4 * x) t.val)) (s : ℕ), s ≤ t.val →
            X (Function.update ω t j) s = X ω s :=
          fun ω t j s hs => Xp_update hreg (rr x) C₀ (tau x) A π hπE ω t j s hs
        have hmono : ∀ ω (s : ℕ), s < 4 * x → X ω s ⊆ X ω (s + 1) :=
          fun ω s hs => Xp_mono hreg (rr x) C₀ (tau x) A π (fun s _ => tau_mono hx1 s)
            (fun s hs => tau_le hx64 s hs) ω s hs
        have hproc := halvingX (C0' hreg C₀) X hXupd hmono hC'
        have hwit : ∀ z, pAX (C0' hreg C₀) (4 * x) X z ≠ 0 → ∀ t : Fin (4 * x),
            (z.2 t.castSucc).card ≤ rr x → ∃ W ∈ z.1 t.castSucc, W ⊆ z.2 t.castSucc := by
          intro z hz t hXt
          obtain ⟨ω, rfl⟩ := mem_support_pAX (C0' hreg C₀) (4 * x) X z hz
          exact Xp_witness hreg (rr x) C₀ hC hne hr1 (tau x) A π hπI ω t.val t.isLt hXt
        have h41 := lemma_4_1 (C0' hreg C₀) hexp' hC' (pAX (C0' hreg C₀) (4 * x) X) hproc hwit
        rw [terminal_pAX] at h41
        refine h41.trans (le_of_eq ?_)
        refine Finset.sum_congr rfl fun ω _ => ?_
        rw [Xp_last]
      · exact hgood)
  obtain ⟨hopt1, hoptk⟩ := opt_bounds (β := bb x) hreg (rr x) x C₀ hC hCk hx1 hkr ω hN
  refine ⟨inst (β := bb x) hreg (rr x) C₀ ω, inst_distinct hreg (rr x) C₀ ω hβ, hopt1, ?_⟩
  refine le_trans ?_ hω
  apply final_ineq m x hx64 _ _ hoptk
  -- `m^{1/3} ≤ 4 (x + 1)`
  have h1 : (m : ℝ) ≤ (4 * ((x : ℝ) + 1)) ^ 3 := by
    have : (m : ℝ) < 64 * ((x : ℝ) + 1) ^ 3 := by exact_mod_cast hxm'
    nlinarith
  calc (m : ℝ) ^ ((1 : ℝ) / 3) ≤ ((4 * ((x : ℝ) + 1)) ^ 3) ^ ((1 : ℝ) / 3) :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) h1 (by norm_num)
    _ = 4 * ((x : ℝ) + 1) := by
        rw [show ((1 : ℝ) / 3) = ((3 : ℕ) : ℝ)⁻¹ by norm_num]
        exact Real.pow_rpow_inv_natCast (by positivity) (by norm_num)

end RandOnlineSetCoverSqrt.LowerBound.Supplement
end

theorem solution : type_of% @RandOnlineSetCoverSqrt.LowerBound.Supplement.chk_theorem_1_4 := @RandOnlineSetCoverSqrt.LowerBound.Supplement.chk_theorem_1_4
