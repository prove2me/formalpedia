-- Prove2me | solution 1 for RandOnlineSetCoverSqrt.LowerBound.theorem_1_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T18:49:14.978441+00:00
-- url     : https://prove2.me/submissions/e801b4b1-bd1f-4cba-a11e-25b9355a97dc

import Mathlib
import Definitions.Def_RandOnlineSetCoverSqrt_LowerBound_Halving
import Theorems.Thm_RandOnlineSetCoverSqrt_LowerBound_lemma_3_1
import Theorems.Thm_RandOnlineSetCoverSqrt_LowerBound_lemma_3_5
import Theorems.Thm_RandOnlineSetCoverSqrt_LowerBound_lemma_4_1

section
set_option autoImplicit false

open scoped ENNReal

namespace RandOnlineSetCoverSqrt.Dev.T12
open RandOnlineSetCoverSqrt.LowerBound RandOnlineSetCover.InfoLB

/-! ### Section 1: batches, the probability space, the chain of families -/

section Chain

variable {m : ℕ}

/-- The forcing batch of `D` supplied by Lemma 3.1 (empty in degenerate cases). -/
noncomputable def batch (r : ℕ) (D : Family m) : List (Element m) :=
  if h : D.Nonempty ∧ (∀ W ∈ D, W.Nonempty) ∧ 1 ≤ r then
    (lemma_3_1 D h.1 h.2.1 r h.2.2).choose
  else []

theorem batch_length_le (r : ℕ) (D : Family m) : (batch r D).length ≤ batchBound m r := by
  unfold batch
  split_ifs with h
  · exact (lemma_3_1 D h.1 h.2.1 r h.2.2).choose_spec.2
  · simp

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

/-! ### Section 2: the request sequence, the instance, the algorithm's purchases -/

section Instance

variable {m : ℕ}

/-- Incidences of batches `0, …, s`. -/
noncomputable def pre (r : ℕ) (C₀ : Family m) {T : ℕ} (ω : Omega T) : ℕ → List (Finset (Fin m))
  | 0 => incidences (batch r (cN C₀ ω 0))
  | s + 1 => pre r C₀ ω s ++ incidences (batch r (cN C₀ ω (s + 1)))

theorem pre_congr (r : ℕ) (C₀ : Family m) {T : ℕ} (ω ω' : Omega T) (s : ℕ)
    (h : ∀ u, u ≤ s → cN C₀ ω u = cN C₀ ω' u) : pre r C₀ ω s = pre r C₀ ω' s := by
  induction s with
  | zero => simp [pre, h 0 le_rfl]
  | succ s ih => simp [pre, ih (fun u hu => h u (by omega)), h (s + 1) le_rfl]

theorem pre_length_le (r : ℕ) (C₀ : Family m) {T : ℕ} (ω : Omega T) (s : ℕ) :
    (pre r C₀ ω s).length ≤ (s + 1) * batchBound m r := by
  induction s with
  | zero => simpa [pre, incidences] using batch_length_le r _
  | succ s ih =>
    simp only [pre, List.length_append, incidences, List.length_map]
    have := batch_length_le r (cN C₀ ω (s + 1))
    nlinarith

theorem pre_prefix (r : ℕ) (C₀ : Family m) {T : ℕ} (ω : Omega T) :
    ∀ s s', s ≤ s' → pre r C₀ ω s <+: pre r C₀ ω s' := by
  intro s s' h
  induction s' with
  | zero => rw [Nat.le_zero.mp h]
  | succ s' ih =>
    rcases Nat.of_le_succ h with h | h
    · exact (ih h).trans (List.prefix_append _ _)
    · rw [h]

theorem mem_pre (r : ℕ) (C₀ : Family m) {T : ℕ} (ω : Omega T) (s u : ℕ) (hu : u ≤ s)
    (e : Finset (Fin m)) (he : e ∈ incidences (batch r (cN C₀ ω u))) : e ∈ pre r C₀ ω s := by
  refine (pre_prefix r C₀ ω u s hu).subset ?_
  cases u with
  | zero => simpa [pre] using he
  | succ u => simp [pre, he]

theorem pre_nonempty (r : ℕ) (C₀ : Family m) {T : ℕ} (ω : Omega T) (s : ℕ) :
    ∀ e ∈ pre r C₀ ω s, e.Nonempty := by
  induction s with
  | zero =>
    intro e he
    simp only [pre, incidences, List.mem_map] at he
    obtain ⟨u, _, rfl⟩ := he
    exact u.2
  | succ s ih =>
    intro e he
    simp only [pre, List.mem_append, incidences, List.mem_map] at he
    rcases he with he | ⟨u, _, rfl⟩
    · exact ih e he
    · exact u.2

/-- The instance: all batches, then universal padding. -/
noncomputable def inst (n r : ℕ) (C₀ : Family m) {T : ℕ} (hm : 0 < m) (ω : Omega T) :
    Instance m n :=
  ⟨fun i => (pre r C₀ ω T)[i.val]?.getD Finset.univ, by
    intro i
    show ((pre r C₀ ω T)[i.val]?.getD Finset.univ).Nonempty
    rcases h : (pre r C₀ ω T)[i.val]? with _ | e
    · rw [Option.getD_none]
      exact Finset.univ_nonempty_iff.mpr ⟨(⟨0, hm⟩ : Fin m)⟩
    · rw [Option.getD_some]
      exact pre_nonempty r C₀ ω T e (List.mem_of_getElem? h)⟩

theorem ofFn_inst (n r : ℕ) (C₀ : Family m) {T : ℕ} (hm : 0 < m) (ω : Omega T)
    (hn : (pre r C₀ ω T).length ≤ n) :
    List.ofFn (inst n r C₀ hm ω).val =
      pre r C₀ ω T ++ List.replicate (n - (pre r C₀ ω T).length) Finset.univ := by
  apply List.ext_getElem
  · simp; omega
  · intro i h1 h2
    simp only [List.getElem_ofFn, inst]
    rw [List.getElem_append]
    split_ifs with h
    · simp [h]
    · rw [List.getElem?_eq_none (by omega), List.getElem_replicate]; rfl

theorem pre_prefix_inst (n r : ℕ) (C₀ : Family m) {T : ℕ} (hm : 0 < m) (ω : Omega T)
    (hn : (pre r C₀ ω T).length ≤ n) (s : ℕ) (hs : s ≤ T) :
    pre r C₀ ω s <+: List.ofFn (inst n r C₀ hm ω).val := by
  rw [ofFn_inst n r C₀ hm ω hn]
  exact (pre_prefix r C₀ ω s T hs).trans (List.prefix_append _ _)

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

/-- The purchases `X_s` after batches `0, …, s`. -/
noncomputable def Xs {n : ℕ} (A : Rule m n) (r : ℕ) (C₀ : Family m) {T : ℕ} (ω : Omega T)
    (s : ℕ) : Finset (Fin m) :=
  chosen A (pre r C₀ ω s)

/-- Validity: `X_s` meets every request of batches `0, …, s`. -/
theorem Xs_covers {n : ℕ} (A : DetAlg m n) (r : ℕ) (C₀ : Family m) {T : ℕ} (hm : 0 < m)
    (ω : Omega T) (hn : (pre r C₀ ω T).length ≤ n) (s : ℕ) (hs : s ≤ T) :
    ∀ e ∈ pre r C₀ ω s, (Xs A.val r C₀ ω s ∩ e).Nonempty := by
  intro e he
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp he
  have hpref := pre_prefix_inst n r C₀ hm ω hn s hs
  have hin : i < n := by
    have := hpref.length_le
    simp only [List.length_ofFn] at this
    omega
  have hval := A.2 ⟨Fin.last n, (inst n r C₀ hm ω).val⟩ ⟨i, hin⟩ ((inst n r C₀ hm ω).2 ⟨i, hin⟩)
  have heq : (inst n r C₀ hm ω).val ⟨i, hin⟩ = (pre r C₀ ω s)[i] := by
    have := hpref.getElem hi
    rw [this]; simp
  have htake : (List.ofFn (inst n r C₀ hm ω).val).take (i + 1) =
      (pre r C₀ ω s).take (i + 1) := by
    rw [List.prefix_iff_eq_take.mp hpref, List.take_take]
    congr 1; omega
  simp only at hval
  rw [htake, heq] at hval
  obtain ⟨x, hx⟩ := hval
  refine ⟨x, ?_⟩
  simp only [Finset.mem_inter] at hx ⊢
  exact ⟨chosen_mono A.val (List.take_prefix _ _) hx.1, hx.2⟩

end Instance

/-! ### Section 3: the trajectory law and the halving process -/

section Law

variable {m : ℕ}

/-- The trajectory `(C^t, X_t)_{t ≤ T}` for a coin vector `ω`. -/
noncomputable def traj {n : ℕ} (A : Rule m n) (r : ℕ) (C₀ : Family m) {T : ℕ} (ω : Omega T) :
    Trajectory m T :=
  (fun s => cN C₀ ω s.val, fun s => Xs A r C₀ ω s.val)

/-- The law `p_A` of the trajectory. -/
noncomputable def pA {n : ℕ} (A : Rule m n) (r : ℕ) (C₀ : Family m) (T : ℕ) :
    PMF (Trajectory m T) :=
  (PMF.uniformOfFintype (Omega T)).map (traj A r C₀)

theorem mem_support_pA {n : ℕ} (A : Rule m n) (r : ℕ) (C₀ : Family m) (T : ℕ)
    (z : Trajectory m T) (hz : pA A r C₀ T z ≠ 0) : ∃ ω : Omega T, traj A r C₀ ω = z := by
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

/-- The history through `t` does not read coordinate `t`. -/
theorem traj_update {n : ℕ} (A : Rule m n) (r : ℕ) (C₀ : Family m) {T : ℕ} (ω : Omega T)
    (t : Fin T) (j : Fin (Nn T t.val)) (s : ℕ) (hs : s ≤ t.val) :
    cN C₀ (Function.update ω t j) s = cN C₀ ω s ∧
      Xs A r C₀ (Function.update ω t j) s = Xs A r C₀ ω s := by
  have hc : ∀ u, u ≤ s → cN C₀ (Function.update ω t j) u = cN C₀ ω u := by
    intro u hu
    apply cN_congr
    intro v hv
    have : v ≠ t := by intro h; subst h; omega
    simp [Function.update_of_ne this]
  refine ⟨hc s le_rfl, ?_⟩
  unfold Xs
  rw [pre_congr r C₀ _ ω s hc]

theorem halving_eq {n : ℕ} (A : Rule m n) (r : ℕ) (C₀ : Family m) {T : ℕ}
    (hC : C₀.card = 2 ^ T) (t : Fin T) (h : Trajectory m T) (D : Family m) :
    eventMass (pA A r C₀ T) (fun z => sameHistory t z h ∧ z.1 t.succ = D) =
      if D ⊆ h.1 t.castSucc ∧ D.card = (h.1 t.castSucc).card / 2 then
        eventMass (pA A r C₀ T) (fun z => sameHistory t z h) /
          (Nat.choose (h.1 t.castSucc).card ((h.1 t.castSucc).card / 2) : ℝ≥0∞)
      else 0 := by
  classical
  unfold pA
  rw [eventMass_map, eventMass_map]
  have hP : ∀ ω (j : Fin (Nn T t.val)), sameHistory t (traj A r C₀ (Function.update ω t j)) h ↔
      sameHistory t (traj A r C₀ ω) h := by
    intro ω j
    simp only [sameHistory, traj]
    constructor
    · intro H s hs
      obtain ⟨h1, h2⟩ := traj_update A r C₀ ω t j s.val hs
      rw [← h1, ← h2]; exact H s hs
    · intro H s hs
      obtain ⟨h1, h2⟩ := traj_update A r C₀ ω t j s.val hs
      rw [h1, h2]; exact H s hs
  have hsucc : ∀ ω : Omega T, (traj A r C₀ ω).1 t.succ = cN C₀ ω (t.val + 1) := fun ω => rfl
  suffices main : ((Finset.univ.filter (fun ω => sameHistory t (traj A r C₀ ω) h ∧
      (traj A r C₀ ω).1 t.succ = D)).card : ℝ≥0∞) / Fintype.card (Omega T) =
      if D ⊆ h.1 t.castSucc ∧ D.card = (h.1 t.castSucc).card / 2 then
        ((Finset.univ.filter (fun ω => sameHistory t (traj A r C₀ ω) h)).card : ℝ≥0∞) /
          Fintype.card (Omega T) /
          (Nat.choose (h.1 t.castSucc).card ((h.1 t.castSucc).card / 2) : ℝ≥0∞)
      else 0 by convert main
  by_cases hne : ∃ ω₀, sameHistory t (traj A r C₀ ω₀) h
  · obtain ⟨ω₀, h₀⟩ := hne
    have hcE : ∀ ω, sameHistory t (traj A r C₀ ω) h → cN C₀ ω t.val = h.1 t.castSucc :=
      fun ω hω => (hω t.castSucc (by simp)).1
    have hcard : (h.1 t.castSucc).card = 2 ^ (T - t.val) := by
      rw [← hcE ω₀ h₀]; exact (cN_card C₀ hC ω₀ t.val t.isLt.le).1
    have hlen : (halvesList (h.1 t.castSucc)).length = Nn T t.val := by
      rw [halvesList_length, hcard]; rfl
    have hval : ∀ ω, sameHistory t (traj A r C₀ ω) h → cN C₀ ω (t.val + 1) =
        (halvesList (h.1 t.castSucc))[(ω t).val]'(by rw [hlen]; exact (ω t).isLt) := by
      intro ω hω
      rw [cN_succ, hcE ω hω, List.getD_eq_getElem]
    split_ifs with hD
    · have hDmem : D ∈ halvesList (h.1 t.castSucc) := mem_halvesList.mpr hD
      obtain ⟨j, hj, hjD⟩ := List.mem_iff_getElem.mp hDmem
      let jj : Fin (Nn T t.val) := ⟨j, by rw [← hlen]; exact hj⟩
      have hfilt : (Finset.univ.filter
          (fun ω => sameHistory t (traj A r C₀ ω) h ∧ (traj A r C₀ ω).1 t.succ = D)) =
          Finset.univ.filter (fun ω => sameHistory t (traj A r C₀ ω) h ∧ ω t = jj) := by
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
      rw [hfilt, ← slice_card (fun ω => sameHistory t (traj A r C₀ ω) h) t hP jj, hcard]
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
          (fun ω => sameHistory t (traj A r C₀ ω) h ∧ (traj A r C₀ ω).1 t.succ = D)) = ∅ := by
        apply Finset.filter_false_of_mem
        rintro ω - ⟨hω, hω2⟩
        apply hD
        rw [← mem_halvesList, ← hω2, hsucc, hval ω hω]
        exact List.getElem_mem _
      rw [hfilt]; simp
  · push Not at hne
    have h1 : (Finset.univ.filter
        (fun ω => sameHistory t (traj A r C₀ ω) h ∧ (traj A r C₀ ω).1 t.succ = D)) = ∅ :=
      Finset.filter_false_of_mem (fun ω _ hω => hne ω hω.1)
    have h2 : (Finset.univ.filter (fun ω => sameHistory t (traj A r C₀ ω) h)) = ∅ :=
      Finset.filter_false_of_mem (fun ω _ hω => hne ω hω)
    rw [h1, h2]; simp

theorem halving {n : ℕ} (A : Rule m n) (r : ℕ) (C₀ : Family m) {T : ℕ}
    (hC : C₀.card = 2 ^ T) : HalvingProcess (pA A r C₀ T) C₀ := by
  refine ⟨?_, ?_, fun t h D => halving_eq A r C₀ hC t h D⟩
  · intro z hz
    obtain ⟨ω, rfl⟩ := mem_support_pA A r C₀ T z hz
    rfl
  · intro z hz t
    obtain ⟨ω, rfl⟩ := mem_support_pA A r C₀ T z hz
    exact chosen_mono A (pre_prefix r C₀ ω _ _ (by simp))

/-- `hwitness` of Lemma 4.1 for `p_A`, from validity and the forcing property. -/
theorem witness {n : ℕ} (A : DetAlg m n) (r : ℕ) (C₀ : Family m) {T : ℕ} (hm : 0 < m)
    (hC : C₀.card = 2 ^ T) (hne : ∀ W ∈ C₀, W.Nonempty) (hr : 1 ≤ r)
    (hn : (T + 1) * batchBound m r ≤ n) :
    ∀ z, pA A.val r C₀ T z ≠ 0 → ∀ t : Fin T,
      (z.2 t.castSucc).card ≤ r → ∃ W ∈ z.1 t.castSucc, W ⊆ z.2 t.castSucc := by
  intro z hz t hX
  obtain ⟨ω, rfl⟩ := mem_support_pA A.val r C₀ T z hz
  have hcard := cN_card C₀ hC ω t.val t.isLt.le
  have hD : (cN C₀ ω t.val).Nonempty := Finset.card_pos.mp (by rw [hcard.1]; positivity)
  have hF := batch_forcing r (cN C₀ ω t.val) hD (fun W hW => hne W (hcard.2 hW)) hr
  have hlen : (pre r C₀ ω T).length ≤ n := (pre_length_le r C₀ ω T).trans hn
  refine (hF _ hX).mp ?_
  intro e he
  exact Xs_covers A r C₀ hm ω hlen t.val t.isLt.le e (mem_pre r C₀ ω t.val t.val le_rfl e he)

/-- `E[|X_T|] ≤ E[cost]` for `p_A`. -/
theorem terminal_le {n : ℕ} (A : DetAlg m n) (r : ℕ) (C₀ : Family m) {T : ℕ} (hm : 0 < m)
    (hn : (T + 1) * batchBound m r ≤ n) :
    terminalExpectation (pA A.val r C₀ T) ≤
      ∑ ω : Omega T, (Fintype.card (Omega T) : ℝ)⁻¹ * (cost A (inst n r C₀ hm ω) : ℝ) := by
  unfold pA
  rw [terminal_map]
  apply Finset.sum_le_sum
  intro ω _
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hlen : (pre r C₀ ω T).length ≤ n := (pre_length_le r C₀ ω T).trans hn
  exact_mod_cast Finset.card_le_card
    (chosen_mono A.val (pre_prefix_inst n r C₀ hm ω hlen T le_rfl))

end Law

/-! ### Section 4: the optimum of each instance -/

section OptSec

variable {m : ℕ}

theorem mem_pre_exists (r : ℕ) (C₀ : Family m) {T : ℕ} (ω : Omega T) (s : ℕ) :
    ∀ e ∈ pre r C₀ ω s, ∃ u ≤ s, e ∈ incidences (batch r (cN C₀ ω u)) := by
  induction s with
  | zero => intro e he; exact ⟨0, le_rfl, by simpa [pre] using he⟩
  | succ s ih =>
    intro e he
    simp only [pre, List.mem_append] at he
    rcases he with he | he
    · obtain ⟨u, hu, h⟩ := ih e he
      exact ⟨u, by omega, h⟩
    · exact ⟨s + 1, le_rfl, he⟩

theorem opt_bounds (n r k : ℕ) (C₀ : Family m) {T : ℕ} (hm : 0 < m) (hC : C₀.card = 2 ^ T)
    (hk : ∀ W ∈ C₀, W.card = k) (hk1 : 1 ≤ k) (hkr : k ≤ r)
    (hn : (T + 1) * batchBound m r ≤ n) (hn0 : 0 < n) (ω : Omega T) :
    1 ≤ Opt (inst n r C₀ hm ω) ∧ Opt (inst n r C₀ hm ω) ≤ k := by
  have hT := cN_card C₀ hC ω T le_rfl
  rw [Nat.sub_self, pow_zero] at hT
  obtain ⟨W, hW⟩ := Finset.card_eq_one.mp hT.1
  have hWT : W ∈ cN C₀ ω T := by rw [hW]; exact Finset.mem_singleton_self W
  have hWk : W.card = k := hk W (hT.2 hWT)
  have hWne : W.Nonempty := Finset.card_pos.mp (by omega)
  have hlen : (pre r C₀ ω T).length ≤ n := (pre_length_le r C₀ ω T).trans hn
  have hcov : Covers (List.ofFn (inst n r C₀ hm ω).val) W := by
    intro e he
    rw [ofFn_inst n r C₀ hm ω hlen, List.mem_append] at he
    rcases he with he | he
    · obtain ⟨u, hu, heu⟩ := mem_pre_exists r C₀ ω T e he
      have hcu := cN_card C₀ hC ω u hu
      have hD : (cN C₀ ω u).Nonempty := Finset.card_pos.mp (by rw [hcu.1]; positivity)
      have hF := batch_forcing r (cN C₀ ω u) hD
        (fun W' hW' => Finset.card_pos.mp (by rw [hk W' (hcu.2 hW')]; omega)) (by omega)
      have hWu : W ∈ cN C₀ ω u := cN_antitone C₀ hC ω u T hu le_rfl hWT
      exact (hF W (by omega)).mpr ⟨W, hWu, subset_rfl⟩ e heu
    · rw [(List.mem_replicate.mp he).2, Finset.inter_univ]; exact hWne
  have hle : listOpt (List.ofFn (inst n r C₀ hm ω).val) ≤ k := by
    unfold listOpt
    exact iInf_le_of_le ⟨W, hcov⟩ (by simp [hWk])
  have hge : 1 ≤ listOpt (List.ofFn (inst n r C₀ hm ω).val) := by
    unfold listOpt
    refine le_iInf fun C => ?_
    have he : (inst n r C₀ hm ω).val ⟨0, hn0⟩ ∈ List.ofFn (inst n r C₀ hm ω).val :=
      List.mem_ofFn.mpr ⟨_, rfl⟩
    obtain ⟨x, hx⟩ := C.2 _ he
    have : 1 ≤ C.val.card := Finset.card_pos.mpr ⟨x, (Finset.mem_inter.mp hx).1⟩
    exact_mod_cast this
  have hne : listOpt (List.ofFn (inst n r C₀ hm ω).val) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.natCast_ne_top k) hle
  refine ⟨?_, ENat.toNat_le_of_le_natCast hle⟩
  unfold Opt
  have h' := ENat.natCast_toNat hne
  rw [← h'] at hge
  exact_mod_cast hge

end OptSec

/-! ### Section 5: Yao's averaging and the constants -/

section Yao

variable {m : ℕ}

theorem pmf_sum_toReal {α : Type*} [Fintype α] (p : PMF α) : ∑ a, (p a).toReal = 1 := by
  have h := p.tsum_coe
  rw [tsum_fintype] at h
  rw [← ENNReal.toReal_sum (fun a _ => p.apply_ne_top a), h, ENNReal.toReal_one]

theorem yao {Ω : Type*} [Fintype Ω] [Nonempty Ω] {n : ℕ} (I : Ω → Instance m n) (L : ℝ)
    (R : RandAlg m n)
    (h : ∀ A : DetAlg m n, L ≤ ∑ ω, (Fintype.card Ω : ℝ)⁻¹ * (cost A (I ω) : ℝ)) :
    ∃ ω, L ≤ expectedCost R (I ω) := by
  by_contra hcon
  push Not at hcon
  set w : ℝ := (Fintype.card Ω : ℝ)⁻¹
  have hw : 0 < w := by positivity
  have hsum : ∑ _ω : Ω, w * L = L := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc, mul_inv_cancel₀ (by positivity),
      one_mul]
  have hlt : ∑ ω, w * expectedCost R (I ω) < ∑ _ω : Ω, w * L :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
      (fun ω _ => mul_lt_mul_of_pos_left (hcon ω) hw)
  have hswap : ∑ ω, w * expectedCost R (I ω) =
      ∑ A, (R A).toReal * ∑ ω, w * (cost A (I ω) : ℝ) := by
    unfold expectedCost
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun A _ => Finset.sum_congr rfl fun ω _ => by ring
  have hge : L ≤ ∑ A, (R A).toReal * ∑ ω, w * (cost A (I ω) : ℝ) := by
    calc L = ∑ A, (R A).toReal * L := by rw [← Finset.sum_mul, pmf_sum_toReal, one_mul]
      _ ≤ _ := Finset.sum_le_sum fun A _ =>
          mul_le_mul_of_nonneg_left (h A) ENNReal.toReal_nonneg
  linarith

theorem constants (m : ℕ) (hm : 64 ≤ m) :
    (m : ℝ) / 128 ≤ (1 - Real.exp (-(qParam m : ℝ) / 4)) * (rParam m : ℝ) := by
  have hsq : (8 : ℝ) ≤ Real.sqrt m := by
    rw [show (8 : ℝ) = Real.sqrt 64 by
      rw [show (64 : ℝ) = 8 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hm)
  have hq : (8 : ℝ) ≤ qParam m := hsq.trans (Nat.le_ceil _)
  have hexp : Real.exp (-(qParam m : ℝ) / 4) ≤ 1 / 2 := by
    have h1 : Real.exp (-(qParam m : ℝ) / 4) ≤ Real.exp (-2) :=
      Real.exp_le_exp.mpr (by linarith)
    have h2 : 2 + 1 ≤ Real.exp 2 := Real.add_one_le_exp 2
    have h3 : Real.exp (-2) * Real.exp 2 = 1 := by rw [← Real.exp_add]; simp
    have h4 : 0 < Real.exp (-2) := Real.exp_pos _
    nlinarith
  have hr : (m : ℝ) ≤ 32 * (rParam m : ℝ) + 31 := by
    have : m ≤ 32 * (m / 32) + 31 := by omega
    unfold rParam
    exact_mod_cast this
  have hm' : (64 : ℝ) ≤ m := by exact_mod_cast hm
  have hr0 : (0 : ℝ) ≤ rParam m := Nat.cast_nonneg _
  nlinarith

end Yao

end RandOnlineSetCoverSqrt.Dev.T12

namespace RandOnlineSetCoverSqrt.LowerBound
open RandOnlineSetCoverSqrt.Dev.T12 RandOnlineSetCover.InfoLB in
theorem chk_theorem_1_2 :
    ∃ c : ℝ, 0 < c ∧ ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m →
      ∀ R : RandOnlineSetCover.InfoLB.RandAlg m (horizon m),
      ∃ I : RandOnlineSetCover.InfoLB.Instance m (horizon m),
        0 < horizon m ∧
        1 ≤ RandOnlineSetCover.InfoLB.Opt I ∧
        RandOnlineSetCover.InfoLB.Opt I ≤ kParam m ∧
        (1 - Real.exp (-(qParam m : ℝ) / 4)) * (rParam m : ℝ) ≤
          RandOnlineSetCover.InfoLB.expectedCost R I ∧
        c * Real.sqrt (m : ℝ) * (RandOnlineSetCover.InfoLB.Opt I : ℝ) ≤
          RandOnlineSetCover.InfoLB.expectedCost R I := by
  obtain ⟨m₁, hm₁⟩ := lemma_3_5
  refine ⟨1 / 128, by norm_num, max m₁ 64, le_max_of_le_right (by norm_num), ?_⟩
  intro m hm R
  obtain ⟨C₀, hcard, hexp⟩ := hm₁ m (le_of_max_le_left hm)
  have h64 : 64 ≤ m := le_of_max_le_right hm
  obtain ⟨hk1, hkr, hrm, hq2, hCk, -⟩ := id hexp
  have hmpos : 0 < m := by omega
  have hr : 1 ≤ rParam m := hk1.trans hkr
  have hne : ∀ W ∈ C₀, W.Nonempty := fun W hW => Finset.card_pos.mp (by rw [hCk W hW]; omega)
  have hC : C₀.card = 2 ^ (4 * qParam m) := hcard
  have hn : (4 * qParam m + 1) * batchBound m (rParam m) ≤ horizon m := le_rfl
  have hbb : 0 < batchBound m (rParam m) := by
    unfold batchBound
    exact Finset.sum_pos' (fun _ _ => Nat.zero_le _) ⟨0, by simp, by simp⟩
  have hhor : 0 < horizon m := Nat.mul_pos (by omega) hbb
  obtain ⟨ω, hω⟩ := yao (fun ω : Omega (4 * qParam m) => inst (horizon m) (rParam m) C₀ hmpos ω)
    ((1 - Real.exp (-(qParam m : ℝ) / 4)) * (rParam m : ℝ)) R
    (fun A => (lemma_4_1 C₀ hexp hC (pA A.val (rParam m) C₀ (4 * qParam m))
      (halving A.val (rParam m) C₀ hC)
      (witness A (rParam m) C₀ hmpos hC hne hr hn)).trans (terminal_le A (rParam m) C₀ hmpos hn))
  obtain ⟨hopt1, hoptk⟩ := opt_bounds (horizon m) (rParam m) (kParam m) C₀ hmpos hC hCk hk1 hkr
    hn hhor ω
  refine ⟨inst (horizon m) (rParam m) C₀ hmpos ω, hhor, hopt1, hoptk, hω, ?_⟩
  have hk : (kParam m : ℝ) ≤ Real.sqrt m := Nat.floor_le (Real.sqrt_nonneg _)
  have hopt : (Opt (inst (horizon m) (rParam m) C₀ hmpos ω) : ℝ) ≤ Real.sqrt m :=
    (Nat.cast_le.mpr hoptk).trans hk
  have hsq : Real.sqrt m * Real.sqrt m = m := Real.mul_self_sqrt (Nat.cast_nonneg _)
  have hs0 : 0 ≤ Real.sqrt m := Real.sqrt_nonneg _
  calc 1 / 128 * Real.sqrt m * (Opt (inst (horizon m) (rParam m) C₀ hmpos ω) : ℝ)
      ≤ 1 / 128 * Real.sqrt m * Real.sqrt m := by gcongr
    _ = (m : ℝ) / 128 := by rw [mul_assoc, hsq]; ring
    _ ≤ _ := constants m h64
    _ ≤ _ := hω

end RandOnlineSetCoverSqrt.LowerBound
end

theorem solution : type_of% @RandOnlineSetCoverSqrt.LowerBound.chk_theorem_1_2 := @RandOnlineSetCoverSqrt.LowerBound.chk_theorem_1_2
