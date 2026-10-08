-- Prove2me | solution 1 for OnlineSetCover.Weighted.theorem_3_4
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-05T16:54:38.743664+00:00
-- url     : https://prove2.me/submissions/966a3a7c-7c88-4621-a195-e5c83c22a884

import Mathlib
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_SetCoverInstance
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_elementWeight
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_coveredBy
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_potential
import Definitions.Def_OnlineSetCover_Weighted_Run

open OnlinePrimalDual.OnlineSetCover


namespace OnlineSetCover.Weighted

theorem wkey_ineq (u y : ℝ) (hu : 0 ≤ u) (hy0 : 0 ≤ y) (hy : y ≤ 1/2) :
    Real.exp (-3*u*y) * ((1 - Real.exp (-2*u)) * Real.exp y + Real.exp (-2*u)) ≤ 1 := by
  have h1 := Real.add_one_le_exp (-2*u)
  have h2 : Real.exp (-2*u) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have h3 : |Real.exp y - 1 - y| ≤ y^2 := Real.abs_exp_sub_one_sub_id_le (by rw [abs_le]; constructor <;> linarith)
  have h3' := (abs_le.mp h3).2
  have h4 := Real.add_one_le_exp (3*u*y)
  have h5 : Real.exp (-3*u*y) * Real.exp (3*u*y) = 1 := by rw [← Real.exp_add]; simp
  have hp0 : 0 ≤ 1 - Real.exp (-2*u) := by linarith
  have hey : 0 ≤ Real.exp y - 1 := by linarith [Real.add_one_le_exp y]
  have h6 : (1 - Real.exp (-2*u)) * Real.exp y + Real.exp (-2*u) ≤ 1 + 3*u*y := by
    have : (1 - Real.exp (-2*u)) * (Real.exp y - 1) ≤ (2*u) * (y + y^2) :=
      mul_le_mul (by linarith) (by linarith) hey (by linarith)
    have h7 : 2*u*(y+y^2) ≤ 3*u*y := by nlinarith [mul_nonneg hu hy0]
    linear_combination this + h7
  have hE := Real.exp_pos (-3*u*y)
  calc _ ≤ Real.exp (-3*u*y) * (1 + 3*u*y) := mul_le_mul_of_nonneg_left h6 hE.le
    _ ≤ Real.exp (-3*u*y) * Real.exp (3*u*y) := mul_le_mul_of_nonneg_left (by linarith) hE.le
    _ = 1 := h5

variable {X T : Type*} [Fintype X] [Fintype T] [DecidableEq T]

theorem wsum_upd (f g : T → ℝ) (S : T) (h : ∀ t, t ≠ S → g t = f t) :
    ∑ t, g t = ∑ t, f t + (g S - f S) := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ S), ← Finset.add_sum_erase _ f (Finset.mem_univ S),
    Finset.sum_congr rfl (fun t ht => h t (Finset.ne_of_mem_erase ht))]
  ring

theorem wew_aug (inst : SetCoverInstance X T) (w : T → ℝ) (S : T) (e : X) :
    elementWeight inst (augmentWeight inst w S) e = elementWeight inst w e +
      (if S ∈ inst.elemSets e then w S / ((Fintype.card X : ℝ) * inst.c S) else 0) := by
  unfold elementWeight augmentWeight
  have : ∀ t ∈ inst.elemSets e, Function.update w S (w S * (1 + 1 / ((Fintype.card X : ℝ) * inst.c S))) t
      = w t + (if t = S then w S / ((Fintype.card X : ℝ) * inst.c S) else 0) := by
    intro t _
    by_cases h : t = S
    · subst h; simp; ring
    · simp [h]
  rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_ite_eq']

open Classical in
theorem wpot_def (inst : SetCoverInstance X T) (w : T → ℝ) (C : Finset T) (α : ℝ) :
    potential inst w C α = (∑ e, if coveredBy inst C e then 0 else
        (Fintype.card X : ℝ) ^ (2 * elementWeight inst w e)) +
      (Fintype.card X : ℝ) * Real.exp ((1 / (2 * α)) *
        ∑ t : T, (inst.c t * (if t ∈ C then (1 : ℝ) else 0) -
          3 * w t * inst.c t * Real.log (Fintype.card X : ℝ))) := by
  unfold potential
  simp only [Finset.sum_filter]
  congr 1
  refine Finset.sum_congr rfl fun e _ => ?_
  by_cases h : coveredBy inst C e <;> simp [h]

theorem wcov_insert (inst : SetCoverInstance X T) (C : Finset T) (S : T) (e : X) :
    coveredBy inst (insert S C) e ↔ coveredBy inst C e ∨ S ∈ inst.elemSets e := by
  unfold coveredBy
  constructor
  · rintro ⟨t, ht, htC⟩
    rcases Finset.mem_insert.mp htC with rfl | h
    · exact Or.inr ht
    · exact Or.inl ⟨t, ht, h⟩
  · rintro (⟨t, ht, htC⟩ | h)
    · exact ⟨t, ht, Finset.mem_insert_of_mem htC⟩
    · exact ⟨S, h, Finset.mem_insert_self _ _⟩

theorem wcov_mem (inst : SetCoverInstance X T) (C : Finset T) (S : T) (e : X) (hS : S ∈ C)
    (he : S ∈ inst.elemSets e) : coveredBy inst C e := ⟨S, he, hS⟩

theorem wpot_empty (inst : SetCoverInstance X T) (w : T → ℝ) (C : Finset T) (α : ℝ)
    (hX : Fintype.card X = 0) : potential inst w C α = 0 := by
  rw [wpot_def]
  haveI : IsEmpty X := Fintype.card_eq_zero_iff.mp hX
  simp [hX]

theorem wsumZ_aug (inst : SetCoverInstance X T) (w : T → ℝ) (C C' : Finset T) (S : T)
    (hCC' : ∀ t, t ≠ S → (t ∈ C' ↔ t ∈ C)) (hN : 0 < (Fintype.card X : ℝ)) :
    ∑ t : T, (inst.c t * (if t ∈ C' then (1 : ℝ) else 0) -
          3 * augmentWeight inst w S t * inst.c t * Real.log (Fintype.card X : ℝ)) =
    ∑ t : T, (inst.c t * (if t ∈ C then (1 : ℝ) else 0) -
          3 * w t * inst.c t * Real.log (Fintype.card X : ℝ)) +
      (inst.c S * ((if S ∈ C' then (1 : ℝ) else 0) - (if S ∈ C then (1 : ℝ) else 0)) -
        3 * (w S / ((Fintype.card X : ℝ) * inst.c S)) * inst.c S * Real.log (Fintype.card X : ℝ)) := by
  rw [wsum_upd _ _ S]
  · congr 1
    have hc := inst.hc_pos S
    simp only [augmentWeight, Function.update_self]
    field_simp
    ring
  · intro t ht
    simp only [augmentWeight, Function.update_of_ne ht]
    by_cases h : t ∈ C
    · simp [h, (hCC' t ht).mpr h]
    · have : t ∉ C' := fun h' => h ((hCC' t ht).mp h')
      simp [h, this]

theorem wprocess_A (inst : SetCoverInstance X T) (α : ℝ) (hα : 0 < α) (w : T → ℝ) (C : Finset T)
    (S : T) (hw : 0 ≤ w S) (hSC : S ∈ C) :
    potential inst (augmentWeight inst w S) C α ≤ potential inst w C α := by
  rcases Nat.eq_zero_or_pos (Fintype.card X) with hX | hX
  · rw [wpot_empty _ _ _ _ hX, wpot_empty _ _ _ _ hX]
  have hN1 : (1 : ℝ) ≤ Fintype.card X := by exact_mod_cast hX
  have hN : (0 : ℝ) < Fintype.card X := by linarith
  rw [wpot_def, wpot_def, wsumZ_aug inst w C C S (fun _ _ => Iff.rfl) hN]
  apply add_le_add
  · apply le_of_eq
    refine Finset.sum_congr rfl fun e _ => ?_
    by_cases hc : coveredBy inst C e
    · simp [hc]
    · have : S ∉ inst.elemSets e := fun h => hc (wcov_mem inst C S e hSC h)
      simp [hc, wew_aug, this]
  · apply mul_le_mul_of_nonneg_left _ hN.le
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hc := inst.hc_pos S
    have : 0 ≤ 3 * (w S / ((Fintype.card X : ℝ) * inst.c S)) * inst.c S *
        Real.log (Fintype.card X : ℝ) := by
      have := Real.log_nonneg hN1
      positivity
    simp only [hSC, if_true, sub_self, mul_zero, zero_sub]
    linarith

open Classical in
theorem wprocess_B (inst : SetCoverInstance X T) (α : ℝ) (hα : 0 < α) (w : T → ℝ) (C : Finset T)
    (S : T) (hw : 0 ≤ w S) (hcα : inst.c S ≤ α) (hSC : S ∉ C) :
    potential inst (augmentWeight inst w S) (insert S C) α ≤ potential inst w C α ∨
    potential inst (augmentWeight inst w S) C α ≤ potential inst w C α := by
  rcases Nat.eq_zero_or_pos (Fintype.card X) with hX | hX
  · left; rw [wpot_empty _ _ _ _ hX, wpot_empty _ _ _ _ hX]
  have hN1 : (1 : ℝ) ≤ Fintype.card X := by exact_mod_cast hX
  have hN : (0 : ℝ) < Fintype.card X := by linarith
  have hc := inst.hc_pos S
  set N : ℝ := (Fintype.card X : ℝ) with hNdef
  set δ : ℝ := w S / (N * inst.c S) with hδ
  have hδ0 : 0 ≤ δ := by positivity
  have hlog : 0 ≤ Real.log N := Real.log_nonneg hN1
  set u : ℝ := δ * Real.log N with hu
  have hu0 : 0 ≤ u := mul_nonneg hδ0 hlog
  set K : ℝ := 1 / (2 * α) with hK
  set y : ℝ := K * inst.c S with hy
  have hy0 : 0 ≤ y := by positivity
  have hy1 : y ≤ 1/2 := by
    rw [hy, hK, div_mul_eq_mul_div, one_mul, div_le_iff₀ (by linarith)]; linarith
  set p : ℝ := 1 - Real.exp (-2*u) with hp
  have hkey := wkey_ineq u y hu0 hy0 hy1
  set Z : ℝ := ∑ t : T, (inst.c t * (if t ∈ C then (1 : ℝ) else 0) -
          3 * w t * inst.c t * Real.log N) with hZ
  have hZ1 := wsumZ_aug inst w C (insert S C) S
    (fun t ht => by simp [Finset.mem_insert, ht]) hN
  have hZ0 := wsumZ_aug inst w C C S (fun _ _ => Iff.rfl) hN
  rw [← hNdef, ← hZ, ← hδ] at hZ1 hZ0
  simp only [Finset.mem_insert_self, if_true, hSC, if_false] at hZ1 hZ0
  set F : ℝ := ∑ e, if coveredBy inst C e then 0 else N ^ (2 * elementWeight inst w e) with hF
  set F1 : ℝ := ∑ e, if coveredBy inst (insert S C) e then 0 else
      N ^ (2 * elementWeight inst (augmentWeight inst w S) e) with hF1
  set F0 : ℝ := ∑ e, if coveredBy inst C e then 0 else
      N ^ (2 * elementWeight inst (augmentWeight inst w S) e) with hF0
  have hrp : ∀ a : ℝ, N ^ (2 * (a + δ)) = N ^ (2 * a) * Real.exp (2 * u) := by
    intro a
    rw [mul_add, Real.rpow_add hN, Real.rpow_def_of_pos hN (2 * δ)]
    congr 2; rw [hu]; ring
  have hFeq : p * F1 + (1 - p) * F0 = F := by
    rw [hF1, hF0, hF, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    by_cases hce : coveredBy inst C e
    · have : coveredBy inst (insert S C) e := (wcov_insert inst C S e).mpr (Or.inl hce)
      simp [hce, this]
    · by_cases hSe : S ∈ inst.elemSets e
      · have : coveredBy inst (insert S C) e := (wcov_insert inst C S e).mpr (Or.inr hSe)
        simp only [hce, this, if_true, if_false, mul_zero, zero_add, wew_aug, hSe]
        rw [← hδ, hrp, hp]
        have : Real.exp (-2*u) * Real.exp (2*u) = 1 := by rw [← Real.exp_add]; simp
        calc (1 - (1 - Real.exp (-2 * u))) * (N ^ (2 * elementWeight inst w e) * Real.exp (2 * u))
            = N ^ (2 * elementWeight inst w e) * (Real.exp (-2*u) * Real.exp (2*u)) := by ring
          _ = _ := by rw [this, mul_one]
      · have : ¬ coveredBy inst (insert S C) e := by
          rw [wcov_insert]; tauto
        simp only [hce, this, if_false, wew_aug, hSe, add_zero]
        ring
  have hE1 : N * Real.exp (K * (Z + (inst.c S * (1 - 0) - 3 * δ * inst.c S * Real.log N))) =
      N * Real.exp (K * Z) * (Real.exp (-3*u*y) * Real.exp y) := by
    rw [show K * (Z + (inst.c S * (1 - 0) - 3 * δ * inst.c S * Real.log N)) = K * Z + (-3*u*y + y)
      by rw [hu, hy]; ring, Real.exp_add, Real.exp_add]; ring
  have hE0 : N * Real.exp (K * (Z + (inst.c S * (0 - 0) - 3 * δ * inst.c S * Real.log N))) =
      N * Real.exp (K * Z) * Real.exp (-3*u*y) := by
    rw [show K * (Z + (inst.c S * (0 - 0) - 3 * δ * inst.c S * Real.log N)) = K * Z + (-3*u*y)
      by rw [hu, hy]; ring, Real.exp_add]; ring
  have hcomb : p * potential inst (augmentWeight inst w S) (insert S C) α +
      (1 - p) * potential inst (augmentWeight inst w S) C α ≤ potential inst w C α := by
    rw [wpot_def, wpot_def, wpot_def, ← hNdef, hZ1, hZ0, ← hZ, ← hK]
    rw [← hF, ← hF1, ← hF0, hE1, hE0]
    have hA : 0 < N * Real.exp (K * Z) := by positivity
    have : p * (N * Real.exp (K * Z) * (Real.exp (-3*u*y) * Real.exp y)) +
        (1 - p) * (N * Real.exp (K * Z) * Real.exp (-3*u*y)) ≤ N * Real.exp (K * Z) := by
      have := mul_le_mul_of_nonneg_left hkey hA.le
      rw [mul_one] at this
      calc _ = N * Real.exp (K * Z) * (Real.exp (-3 * u * y) * (p * Real.exp y + (1 - p))) := by ring
        _ ≤ _ := by
          have e : p * Real.exp y + (1 - p) = (1 - Real.exp (-2*u)) * Real.exp y + Real.exp (-2*u) := by
            rw [hp]; ring
          rw [e]; exact this
    nlinarith [hFeq]
  have hp0 : 0 ≤ p := by
    rw [hp]; have := Real.exp_le_one_iff.mpr (by linarith : -2*u ≤ 0); linarith
  have hp1 : 0 < 1 - p := by rw [hp]; simp [Real.exp_pos]
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h0⟩ := hcon
  have := mul_le_mul_of_nonneg_left h1.le hp0
  have := mul_lt_mul_of_pos_left h0 hp1
  nlinarith

theorem wprocess_ok (inst : SetCoverInstance X T) (α : ℝ) (hα : 0 < α) (w : T → ℝ)
    (C : Finset T) (S : T) (hw : 0 ≤ w S) (hcα : inst.c S ≤ α) :
    ∃ (w' : T → ℝ) (C' : Finset T), processSet inst α w C S = some (w', C') ∧
      potential inst w' C' α ≤ potential inst w C α := by
  unfold processSet
  simp only
  by_cases hSC : S ∈ C
  · have := wprocess_A inst α hα w C S hw hSC
    rw [if_pos hSC, if_pos this]
    exact ⟨_, _, rfl, this⟩
  · rw [if_neg hSC]
    rcases wprocess_B inst α hα w C S hw hcα hSC with h | h
    · rw [if_pos h]; exact ⟨_, _, rfl, h⟩
    · split_ifs with h'
      · exact ⟨_, _, rfl, h'⟩
      · exact ⟨_, _, rfl, h⟩

theorem wps_some (inst : SetCoverInstance X T) (α : ℝ) (w w' : T → ℝ) (C C' : Finset T) (S : T)
    (h : processSet inst α w C S = some (w', C')) :
    w' = augmentWeight inst w S ∧ (∀ t, t ≠ S → (t ∈ C' ↔ t ∈ C)) ∧
      potential inst w' C' α ≤ potential inst w C α := by
  unfold processSet at h
  simp only at h
  split_ifs at h with h1 h2 h3 h4
  · cases h; exact ⟨rfl, fun _ _ => Iff.rfl, h2⟩
  · cases h; exact ⟨rfl, fun t ht => by simp [Finset.mem_insert, ht], h3⟩
  · cases h; exact ⟨rfl, fun _ _ => Iff.rfl, h4⟩

def WInv (inst : SetCoverInstance X T) (σ : List X) (s : AlgState X T) : Prop :=
  (∀ S, 1 / (Fintype.card T : ℝ) ^ 2 ≤ s.w S) ∧
  (∀ S, s.w S ≤ 1 + 1 / ((Fintype.card X : ℝ) * inst.c S)) ∧
  (∀ x ∈ s.pending, x ∈ σ) ∧
  (∀ j l, s.cur = some (j, l) → j ∈ σ ∧ l.Nodup ∧ (∀ S ∈ l, S ∈ inst.elemSets j) ∧
    ∀ S ∈ l, s.w S < 1)

theorem winv_reach (inst : SetCoverInstance X T) (α : ℝ) (σ : List X) {c : Config X T}
    (h : Reachable inst α σ c) : ∀ s, c = .ok s → WInv inst σ s := by
  induction h with
  | init =>
    intro s hs
    cases hs
    refine ⟨fun S => le_refl _, fun S => ?_, fun x hx => hx, fun j l h => by simp [initState] at h⟩
    have hm : (1 : ℝ) ≤ Fintype.card T := by
      exact_mod_cast Fintype.card_pos_iff.mpr ⟨S⟩
    have hc := inst.hc_pos S
    show 1 / (Fintype.card T : ℝ) ^ 2 ≤ _
    have : 1 / (Fintype.card T : ℝ) ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]; nlinarith
    have : 0 ≤ 1 / ((Fintype.card X : ℝ) * inst.c S) := by positivity
    linarith
  | @step s0 c0 hr hst ih =>
    intro s hs
    subst hs
    obtain ⟨I1, I2, I3, I4⟩ := ih _ rfl
    cases hst with
    | arrive j rest hcur hpend =>
      refine ⟨I1, I2, fun x hx => I3 x (by rw [hpend]; exact List.mem_cons_of_mem _ hx), ?_⟩
      intro j' l h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨I3 _ (by rw [hpend]; exact List.mem_cons_self), List.nodup_nil, by simp, by simp⟩
    | finish j hcur _ =>
      exact ⟨I1, I2, I3, fun j l h => by simp at h⟩
    | startStep j l hcur hlt henum =>
      refine ⟨I1, I2, I3, ?_⟩
      intro j' l' h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨(I4 _ _ hcur).1, henum.1, fun S hS => (henum.2 S).mp hS, fun S hS => ?_⟩
      have hS' := (henum.2 S).mp hS
      have hle : s0.w S ≤ elementWeight inst s0.w j := by
        unfold elementWeight
        exact Finset.single_le_sum (f := s0.w) (fun t _ => le_trans (by positivity) (I1 t)) hS'
      exact lt_of_le_of_lt hle hlt
    | process j S l w' C' hcur hps =>
      obtain ⟨hw', _, _⟩ := wps_some inst α _ _ _ _ _ hps
      subst hw'
      obtain ⟨hjσ, hnd, hmem, hlt⟩ := I4 _ _ hcur
      have hc := inst.hc_pos S
      have ha : 0 ≤ 1 / ((Fintype.card X : ℝ) * inst.c S) := by positivity
      have hS1 : s0.w S < 1 := hlt S List.mem_cons_self
      have hpos : 0 ≤ s0.w S := le_trans (by positivity) (I1 S)
      refine ⟨fun t => ?_, fun t => ?_, I3, ?_⟩
      · show _ ≤ augmentWeight inst s0.w S t
        unfold augmentWeight
        by_cases ht : t = S
        · subst ht; simp only [Function.update_self]; nlinarith [I1 t]
        · rw [Function.update_of_ne ht]; exact I1 t
      · show augmentWeight inst s0.w S t ≤ _
        unfold augmentWeight
        by_cases ht : t = S
        · subst ht; simp only [Function.update_self]; nlinarith
        · rw [Function.update_of_ne ht]; exact I2 t
      · intro j' l' h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hnd' := List.nodup_cons.mp hnd
        refine ⟨hjσ, hnd'.2, fun t ht => hmem t (List.mem_cons_of_mem _ ht), fun t ht => ?_⟩
        show augmentWeight inst s0.w S t < 1
        have htS : t ≠ S := fun h => hnd'.1 (h ▸ ht)
        unfold augmentWeight
        rw [Function.update_of_ne htS]
        exact hlt t (List.mem_cons_of_mem _ ht)

theorem lemma_3_3_core (inst : SetCoverInstance X T) (α : ℝ) (hα : 0 < α) :
    (∀ (w : T → ℝ) (C : Finset T) (S : T), 0 ≤ w S → inst.c S ≤ α →
        ∃ (w' : T → ℝ) (C' : Finset T), processSet inst α w C S = some (w', C') ∧
          potential inst w' C' α ≤ potential inst w C α) ∧
      ((∀ S, inst.c S ≤ α) → ∀ σ : List X, ¬ Reachable inst α σ (.fail : Config X T)) := by
  refine ⟨fun w C S hw hc => wprocess_ok inst α hα w C S hw hc, fun hcα σ h => ?_⟩
  cases h with
  | @step s0 c0 hr hst =>
    cases hst with
    | processFail j S l hcur hps =>
      obtain ⟨I1, -⟩ := winv_reach inst α σ hr s0 rfl
      obtain ⟨w', C', h', -⟩ := wprocess_ok inst α hα s0.w s0.C S
        (le_trans (by positivity) (I1 S)) (hcα S)
      rw [hps] at h'
      cases h'

def wcl (s : AlgState X T) : List T := match s.cur with
  | none => []
  | some p => p.2

theorem wcl_some (s : AlgState X T) (j : X) (l : List T) (h : s.cur = some (j, l)) : wcl s = l := by
  simp [wcl, h]

theorem wcl_none (s : AlgState X T) (h : s.cur = none) : wcl s = [] := by
  simp [wcl, h]

theorem wreach_empty (inst : SetCoverInstance X T) (α : ℝ) (σ : List X) [IsEmpty X]
    {c : Config X T} (h : Reachable inst α σ c) : c = .ok (initState σ) := by
  induction h with
  | init => rfl
  | @step s0 c0 hr hst ih =>
    cases hst with
    | arrive j => exact isEmptyElim j
    | finish j => exact isEmptyElim j
    | startStep j => exact isEmptyElim j
    | process j => exact isEmptyElim j
    | processFail j => exact isEmptyElim j

theorem winit_sum (inst : SetCoverInstance X T) (hc_m : ∀ S, inst.c S ≤ (Fintype.card T : ℝ)) :
    ∑ S, 1 / (Fintype.card T : ℝ) ^ 2 * inst.c S ≤ 1 := by
  rcases Nat.eq_zero_or_pos (Fintype.card T) with hT | hT
  · haveI : IsEmpty T := Fintype.card_eq_zero_iff.mp hT
    simp
  · have hm : (0 : ℝ) < Fintype.card T := by exact_mod_cast hT
    calc ∑ S, 1 / (Fintype.card T : ℝ) ^ 2 * inst.c S
        ≤ ∑ S : T, 1 / (Fintype.card T : ℝ) ^ 2 * (Fintype.card T : ℝ) :=
          Finset.sum_le_sum fun S _ => mul_le_mul_of_nonneg_left (hc_m S) (by positivity)
      _ = 1 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; field_simp

theorem w32_inv (inst : SetCoverInstance X T) (α : ℝ) (σ : List X)
    (hn : 1 ≤ (Fintype.card X : ℝ)) (hc_m : ∀ S, inst.c S ≤ (Fintype.card T : ℝ))
    {c : Config X T} (h : Reachable inst α σ c) : ∀ s, c = .ok s →
    ∑ S, s.w S * inst.c S + ((wcl s).map s.w).sum / (Fintype.card X : ℝ) ≤
      1 + (s.steps : ℝ) / (Fintype.card X : ℝ) := by
  induction h with
  | init =>
    intro s hs; cases hs
    simp only [initState, wcl, List.map_nil, List.sum_nil, zero_div, add_zero, Nat.cast_zero]
    exact winit_sum inst hc_m
  | @step s0 c0 hr hst ih =>
    intro s hs
    subst hs
    have IH := ih _ rfl
    obtain ⟨I1, I2, I3, I4⟩ := winv_reach inst α σ hr s0 rfl
    cases hst with
    | arrive j rest hcur hpend =>
      rw [wcl_none s0 hcur] at IH
      rw [wcl_some _ j [] rfl]
      simpa using IH
    | finish j hcur _ =>
      rw [wcl_some s0 j [] hcur] at IH
      rw [wcl_none _ rfl]
      simpa using IH
    | startStep j l hcur hlt henum =>
      rw [wcl_some s0 j [] hcur] at IH
      rw [wcl_some _ j l rfl]
      simp only [List.map_nil, List.sum_nil, zero_div, add_zero] at IH
      have hsum : (l.map s0.w).sum = elementWeight inst s0.w j := by
        rw [← List.sum_toFinset _ henum.1]
        unfold elementWeight
        congr 1
        ext S; simp [henum.2]
      show ∑ S, s0.w S * inst.c S + (l.map s0.w).sum / (Fintype.card X : ℝ) ≤
        1 + ((s0.steps + 1 : ℕ) : ℝ) / (Fintype.card X : ℝ)
      rw [hsum]
      push_cast
      have : elementWeight inst s0.w j / (Fintype.card X : ℝ) ≤ 1 / (Fintype.card X : ℝ) :=
        div_le_div_of_nonneg_right hlt.le (by linarith)
      rw [add_div]
      linarith
    | process j S l w' C' hcur hps =>
      obtain ⟨hw', _, _⟩ := wps_some inst α _ _ _ _ _ hps
      subst hw'
      rw [wcl_some s0 j (S :: l) hcur] at IH
      rw [wcl_some _ j l rfl]
      obtain ⟨_, hnd, _, _⟩ := I4 _ _ hcur
      have hnd' := List.nodup_cons.mp hnd
      have hl : (l.map (augmentWeight inst s0.w S)).sum = (l.map s0.w).sum := by
        congr 1
        refine List.map_congr_left fun t ht => ?_
        have htS : t ≠ S := fun h => hnd'.1 (h ▸ ht)
        unfold augmentWeight; rw [Function.update_of_ne htS]
      show ∑ t, augmentWeight inst s0.w S t * inst.c t +
          (l.map (augmentWeight inst s0.w S)).sum / (Fintype.card X : ℝ) ≤
          1 + (s0.steps : ℝ) / (Fintype.card X : ℝ)
      rw [hl, wsum_upd (fun t => s0.w t * inst.c t) _ S (fun t ht => by
        simp only [augmentWeight, Function.update_of_ne ht])]
      simp only [List.map_cons, List.sum_cons] at IH
      have hc := inst.hc_pos S
      have : augmentWeight inst s0.w S S * inst.c S - s0.w S * inst.c S =
          s0.w S / (Fintype.card X : ℝ) := by
        simp only [augmentWeight, Function.update_self]
        field_simp
        ring
      rw [this]
      rw [add_div] at IH
      linarith

theorem wL0_nonneg :
    0 ≤ Real.log ((Fintype.card T : ℝ) ^ 2 * (1 + 1 / (Fintype.card X : ℝ))) := by
  rcases Nat.eq_zero_or_pos (Fintype.card T) with hT | hT
  · simp [hT]
  · apply Real.log_nonneg
    have hm : (1 : ℝ) ≤ Fintype.card T := by exact_mod_cast hT
    have : (0 : ℝ) ≤ 1 / (Fintype.card X : ℝ) := by positivity
    nlinarith

theorem w31_inv (inst : SetCoverInstance X T) (α : ℝ) (Copt : Finset T) (σ : List X)
    (hn : 1 ≤ (Fintype.card X : ℝ))
    (hcov : ∀ j ∈ σ, coveredBy inst Copt j)
    {c : Config X T} (h : Reachable inst α σ c) : ∀ s, c = .ok s →
    (s.steps : ℝ) ≤ ∑ S ∈ Copt, (Real.log ((Fintype.card T : ℝ) ^ 2 * s.w S) /
        Real.log (1 + 1 / ((Fintype.card X : ℝ) * inst.c S)) +
        (if S ∈ wcl s then (1 : ℝ) else 0)) := by
  induction h with
  | init =>
    intro s hs; cases hs
    simp only [initState, wcl, List.not_mem_nil, if_false, add_zero, Nat.cast_zero]
    apply le_of_eq
    symm
    apply Finset.sum_eq_zero
    intro S _
    have hm : (0 : ℝ) < Fintype.card T := by exact_mod_cast Fintype.card_pos_iff.mpr ⟨S⟩
    rw [mul_one_div_cancel (by positivity), Real.log_one, zero_div]
  | @step s0 c0 hr hst ih =>
    intro s hs
    subst hs
    have IH := ih _ rfl
    obtain ⟨I1, I2, I3, I4⟩ := winv_reach inst α σ hr s0 rfl
    cases hst with
    | arrive j rest hcur hpend =>
      rw [wcl_none s0 hcur] at IH
      rw [wcl_some _ j [] rfl]
      simpa using IH
    | finish j hcur _ =>
      rw [wcl_some s0 j [] hcur] at IH
      rw [wcl_none _ rfl]
      simpa using IH
    | startStep j l hcur hlt henum =>
      rw [wcl_some s0 j [] hcur] at IH
      rw [wcl_some _ j l rfl]
      simp only [List.not_mem_nil, if_false, add_zero] at IH
      show ((s0.steps + 1 : ℕ) : ℝ) ≤ _
      push_cast
      rw [Finset.sum_add_distrib]
      obtain ⟨t, ht, htC⟩ := hcov j (I4 j [] hcur).1
      have : (1 : ℝ) ≤ ∑ S ∈ Copt, (if S ∈ l then (1 : ℝ) else 0) := by
        have := Finset.single_le_sum (f := fun S => if S ∈ l then (1 : ℝ) else 0)
          (fun S _ => by positivity) htC
        simpa [(henum.2 t).mpr ht] using this
      linarith
    | process j S l w' C' hcur hps =>
      obtain ⟨hw', _, _⟩ := wps_some inst α _ _ _ _ _ hps
      subst hw'
      rw [wcl_some s0 j (S :: l) hcur] at IH
      rw [wcl_some _ j l rfl]
      obtain ⟨_, hnd, _, _⟩ := I4 _ _ hcur
      have hnd' := List.nodup_cons.mp hnd
      refine le_of_le_of_eq IH (Finset.sum_congr rfl fun t _ => ?_)
      by_cases htS : t = S
      · subst htS
        have hc := inst.hc_pos t
        have hm : (0 : ℝ) < Fintype.card T := by exact_mod_cast Fintype.card_pos_iff.mpr ⟨t⟩
        have hw0 : 0 < s0.w t := lt_of_lt_of_le (by positivity) (I1 t)
        have ha : 0 < 1 / ((Fintype.card X : ℝ) * inst.c t) := by
          have : (0:ℝ) < Fintype.card X := by linarith
          positivity
        have hL : 0 < Real.log (1 + 1 / ((Fintype.card X : ℝ) * inst.c t)) :=
          Real.log_pos (by linarith)
        simp only [augmentWeight, Function.update_self, List.mem_cons_self, if_true, hnd'.1, if_false]
        have e : Real.log ((Fintype.card T : ℝ) ^ 2 * s0.w t * (1 + 1 / ((Fintype.card X : ℝ) * inst.c t)))
            = Real.log ((Fintype.card T : ℝ) ^ 2 * s0.w t) +
              Real.log (1 + 1 / ((Fintype.card X : ℝ) * inst.c t)) :=
          Real.log_mul (by positivity) (by linarith)
        rw [← mul_assoc, e, add_div, div_self hL.ne']
        ring
      · have : augmentWeight inst s0.w S t = s0.w t := by
          unfold augmentWeight; rw [Function.update_of_ne htS]
        simp only [this, List.mem_cons, htS, false_or]

theorem w31_term (inst : SetCoverInstance X T) (hn : 1 ≤ (Fintype.card X : ℝ))
    (hc_one : ∀ S, 1 ≤ inst.c S) (w : T → ℝ) (S : T) (b : Prop) [Decidable b]
    (h1 : 1 / (Fintype.card T : ℝ) ^ 2 ≤ w S)
    (h2 : w S ≤ 1 + 1 / ((Fintype.card X : ℝ) * inst.c S)) (h3 : b → w S < 1) :
    Real.log ((Fintype.card T : ℝ) ^ 2 * w S) /
        Real.log (1 + 1 / ((Fintype.card X : ℝ) * inst.c S)) + (if b then (1 : ℝ) else 0) ≤
      ((Fintype.card X : ℝ) * inst.c S + 1) *
        Real.log ((Fintype.card T : ℝ) ^ 2 * (1 + 1 / (Fintype.card X : ℝ))) := by
  have hc := hc_one S
  have hm1 : (1 : ℝ) ≤ Fintype.card T := by exact_mod_cast Fintype.card_pos_iff.mpr ⟨S⟩
  have hm : (0 : ℝ) < Fintype.card T := by linarith
  have hN : (0 : ℝ) < Fintype.card X := by linarith
  set N : ℝ := (Fintype.card X : ℝ)
  set M : ℝ := (Fintype.card T : ℝ)
  set a : ℝ := 1 / (N * inst.c S) with ha
  have ha0 : 0 < a := by positivity
  have han : a ≤ 1 / N := by
    rw [ha]; apply one_div_le_one_div_of_le hN; nlinarith
  have hw0 : 0 < w S := lt_of_lt_of_le (by positivity) h1
  have hMw : 1 ≤ M ^ 2 * w S := by
    have := mul_le_mul_of_nonneg_left h1 (by positivity : (0:ℝ) ≤ M ^ 2)
    rwa [mul_one_div_cancel (by positivity)] at this
  set L : ℝ := Real.log (1 + a) with hL
  have hLpos : 0 < L := Real.log_pos (by linarith)
  -- step 1: term ≤ log(M^2 (1+a)) / L
  have step1 : Real.log (M ^ 2 * w S) / L + (if b then (1 : ℝ) else 0) ≤
      Real.log (M ^ 2 * (1 + a)) / L := by
    by_cases hb : b
    · rw [if_pos hb]
      have hlt := h3 hb
      have e : Real.log (M ^ 2 * w S) / L + 1 = Real.log (M ^ 2 * w S * (1 + a)) / L := by
        have e2 : Real.log (M ^ 2 * w S * (1 + a)) = Real.log (M ^ 2 * w S) + L :=
          Real.log_mul (by positivity) (by linarith)
        rw [e2, add_div, div_self hLpos.ne']
      rw [e]
      apply div_le_div_of_nonneg_right _ hLpos.le
      apply Real.log_le_log (by positivity)
      have : w S * (1 + a) ≤ 1 * (1 + a) := mul_le_mul_of_nonneg_right hlt.le (by linarith)
      nlinarith
    · rw [if_neg hb, add_zero]
      apply div_le_div_of_nonneg_right _ hLpos.le
      apply Real.log_le_log (by positivity)
      exact mul_le_mul_of_nonneg_left h2 (by positivity)
  -- step 2
  have hL' : 1 / (N * inst.c S + 1) ≤ L := by
    have := Real.one_sub_inv_le_log_of_pos (by linarith : (0:ℝ) < 1 + a)
    have e : 1 - (1 + a)⁻¹ = 1 / (N * inst.c S + 1) := by
      rw [ha]; field_simp; ring
    rw [← e]; exact this
  have hinvL : 1 / L ≤ N * inst.c S + 1 := by
    rw [div_le_iff₀ hLpos]
    rw [div_le_iff₀ (by positivity)] at hL'
    linarith
  have hlogA : 0 ≤ Real.log (M ^ 2 * (1 + a)) := Real.log_nonneg (by nlinarith)
  have hlogB : Real.log (M ^ 2 * (1 + a)) ≤ Real.log (M ^ 2 * (1 + 1 / N)) :=
    Real.log_le_log (by positivity) (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
  calc _ ≤ Real.log (M ^ 2 * (1 + a)) / L := step1
    _ = Real.log (M ^ 2 * (1 + a)) * (1 / L) := by ring
    _ ≤ Real.log (M ^ 2 * (1 + 1 / N)) * (N * inst.c S + 1) :=
        mul_le_mul hlogB hinvL (by positivity) (le_trans hlogA hlogB)
    _ = _ := by ring

theorem lemma_3_1_core (inst : SetCoverInstance X T) (α : ℝ) (Copt : Finset T) (σ : List X)
    (hc_one : ∀ S, 1 ≤ inst.c S)
    (hcov : ∀ j ∈ σ, coveredBy inst Copt j)
    (hopt : ∑ S ∈ Copt, inst.c S ≤ α)
    (s : AlgState X T) (hs : Reachable inst α σ (.ok s)) :
    (s.steps : ℝ) ≤
        ∑ S ∈ Copt, ((Fintype.card X : ℝ) * inst.c S + 1) *
          Real.log ((Fintype.card T : ℝ) ^ 2 * (1 + 1 / (Fintype.card X : ℝ))) ∧
      ∑ S ∈ Copt, ((Fintype.card X : ℝ) * inst.c S + 1) *
          Real.log ((Fintype.card T : ℝ) ^ 2 * (1 + 1 / (Fintype.card X : ℝ))) ≤
        ((Fintype.card X : ℝ) + 1) * α *
          Real.log ((Fintype.card T : ℝ) ^ 2 * (1 + 1 / (Fintype.card X : ℝ))) := by
  have hL0 := wL0_nonneg (X := X) (T := T)
  have hN0 : (0 : ℝ) ≤ Fintype.card X := by positivity
  constructor
  · rcases Nat.eq_zero_or_pos (Fintype.card X) with hX | hX
    · haveI : IsEmpty X := Fintype.card_eq_zero_iff.mp hX
      have := wreach_empty inst α σ hs
      cases this
      simp only [initState, Nat.cast_zero]
      exact Finset.sum_nonneg fun S _ => mul_nonneg (by have := (inst.hc_pos S).le; positivity) hL0
    · have hn : (1 : ℝ) ≤ Fintype.card X := by exact_mod_cast hX
      obtain ⟨I1, I2, -, I4⟩ := winv_reach inst α σ hs s rfl
      refine le_trans (w31_inv inst α Copt σ hn hcov hs s rfl) (Finset.sum_le_sum fun S _ => ?_)
      apply w31_term inst hn hc_one s.w S _ (I1 S) (I2 S)
      intro hS
      unfold wcl at hS
      rcases hcur : s.cur with _ | ⟨j, l⟩
      · rw [hcur] at hS; simp at hS
      · rw [hcur] at hS; exact (I4 j l hcur).2.2.2 S hS
  · rw [← Finset.sum_mul]
    apply mul_le_mul_of_nonneg_right _ hL0
    calc ∑ S ∈ Copt, ((Fintype.card X : ℝ) * inst.c S + 1)
        ≤ ∑ S ∈ Copt, ((Fintype.card X : ℝ) + 1) * inst.c S :=
          Finset.sum_le_sum fun S _ => by nlinarith [hc_one S]
      _ = ((Fintype.card X : ℝ) + 1) * ∑ S ∈ Copt, inst.c S := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left hopt (by positivity)

theorem lemma_3_2_core (inst : SetCoverInstance X T) (α : ℝ) (Copt : Finset T) (σ : List X)
    (hc_one : ∀ S, 1 ≤ inst.c S)
    (hc_m : ∀ S, inst.c S ≤ (Fintype.card T : ℝ))
    (hcov : ∀ j ∈ σ, coveredBy inst Copt j)
    (hopt : ∑ S ∈ Copt, inst.c S ≤ α)
    (s : AlgState X T) (hs : Reachable inst α σ (.ok s)) :
    ∑ S, s.w S * inst.c S ≤ 1 + (s.steps : ℝ) / (Fintype.card X : ℝ) ∧
      ∑ S, s.w S * inst.c S ≤
        1 + (1 + 1 / (Fintype.card X : ℝ)) * α *
          Real.log ((Fintype.card T : ℝ) ^ 2 * (1 + 1 / (Fintype.card X : ℝ))) := by
  have hL0 := wL0_nonneg (X := X) (T := T)
  have hα0 : 0 ≤ α := le_trans (Finset.sum_nonneg fun S _ => (inst.hc_pos S).le) hopt
  rcases Nat.eq_zero_or_pos (Fintype.card X) with hX | hX
  · haveI : IsEmpty X := Fintype.card_eq_zero_iff.mp hX
    have := wreach_empty inst α σ hs
    cases this
    have h0 := winit_sum inst hc_m
    simp only [initState, hX, Nat.cast_zero, div_zero, add_zero]
    constructor
    · exact h0
    · have : 0 ≤ 1 * α * Real.log ((Fintype.card T : ℝ) ^ 2 * 1) := by
        have h := hL0; simp only [hX, Nat.cast_zero, div_zero, add_zero] at h; positivity
      linarith
  · have hn : (1 : ℝ) ≤ Fintype.card X := by exact_mod_cast hX
    have hN : (0 : ℝ) < Fintype.card X := by linarith
    obtain ⟨I1, -⟩ := winv_reach inst α σ hs s rfl
    have hinv := w32_inv inst α σ hn hc_m hs s rfl
    have hl : 0 ≤ ((wcl s).map s.w).sum / (Fintype.card X : ℝ) := by
      apply div_nonneg _ hN.le
      apply List.sum_nonneg
      intro x hx
      obtain ⟨t, _, rfl⟩ := List.mem_map.mp hx
      exact le_trans (by positivity) (I1 t)
    have h1 : ∑ S, s.w S * inst.c S ≤ 1 + (s.steps : ℝ) / (Fintype.card X : ℝ) := by linarith
    refine ⟨h1, le_trans h1 ?_⟩
    obtain ⟨a1, a2⟩ := lemma_3_1_core inst α Copt σ hc_one hcov hopt s hs
    have : (s.steps : ℝ) ≤ ((Fintype.card X : ℝ) + 1) * α *
        Real.log ((Fintype.card T : ℝ) ^ 2 * (1 + 1 / (Fintype.card X : ℝ))) := le_trans a1 a2
    have e : (1 + 1 / (Fintype.card X : ℝ)) * α *
        Real.log ((Fintype.card T : ℝ) ^ 2 * (1 + 1 / (Fintype.card X : ℝ))) =
        ((Fintype.card X : ℝ) + 1) * α *
        Real.log ((Fintype.card T : ℝ) ^ 2 * (1 + 1 / (Fintype.card X : ℝ))) / (Fintype.card X : ℝ) := by
      field_simp
    rw [e]
    have := div_le_div_of_nonneg_right this hN.le
    linarith

theorem wopd_main {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) (α β : ℝ) (hα_pos : 0 < α) (hβ_nonneg : 0 ≤ β)
    (w : T → ℝ) (hw_nonneg : ∀ t, 0 ≤ w t) (C : Finset T)
    (hE : 1 ≤ Fintype.card E)
    (hfrac : ∑ t : T, w t * inst.c t ≤ β * α)
    (hΦ_bound : potential inst w C α < (Fintype.card E : ℝ) ^ 2) :
    (∀ e : E, 1 ≤ elementWeight inst w e → coveredBy inst C e) ∧
    (∑ t ∈ C, inst.c t ≤ α * Real.log (Fintype.card E : ℝ) * (3 * β + 2)) := by
  classical
  set n : ℝ := (Fintype.card E : ℝ) with hn
  have hn1 : 1 ≤ n := by rw [hn]; exact_mod_cast hE
  have hn0 : 0 < n := by linarith
  set X : ℝ := (1 / (2 * α)) *
      ∑ t : T, (inst.c t * (if t ∈ C then (1 : ℝ) else 0) - 3 * w t * inst.c t * Real.log n)
    with hX
  set S1 : ℝ := ∑ e ∈ Finset.univ.filter (fun e => ¬ coveredBy inst C e),
      n ^ (2 * elementWeight inst w e) with hS1
  have hΦ : potential inst w C α = S1 + n * Real.exp X := by
    simp only [potential, hS1, hX, hn]
  have hS1nn : 0 ≤ S1 := Finset.sum_nonneg fun e _ => Real.rpow_nonneg hn0.le _
  have hexp : 0 < n * Real.exp X := mul_pos hn0 (Real.exp_pos X)
  rw [hΦ] at hΦ_bound
  refine ⟨fun e he => ?_, ?_⟩
  · by_contra hcov
    have hmem : e ∈ Finset.univ.filter (fun e => ¬ coveredBy inst C e) := by simp [hcov]
    have h1 : n ^ (2 * elementWeight inst w e) ≤ S1 :=
      Finset.single_le_sum (f := fun e => n ^ (2 * elementWeight inst w e))
        (fun e _ => Real.rpow_nonneg hn0.le _) hmem
    have h2 : n ^ (2 : ℝ) ≤ n ^ (2 * elementWeight inst w e) :=
      Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
    rw [Real.rpow_two] at h2
    linarith
  · have h1 : n * Real.exp X < n ^ 2 := by linarith
    have h2 : Real.exp X < n := by
      rw [pow_two] at h1
      exact lt_of_mul_lt_mul_left h1 hn0.le
    have h3 : X < Real.log n := by
      rw [← Real.exp_lt_exp, Real.exp_log hn0]; exact h2
    have hsumC : ∑ t : T, inst.c t * (if t ∈ C then (1 : ℝ) else 0) = ∑ t ∈ C, inst.c t := by
      simp only [mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_mem, Finset.univ_inter]
    have hsplit : ∑ t : T, (inst.c t * (if t ∈ C then (1 : ℝ) else 0)
        - 3 * w t * inst.c t * Real.log n) =
        ∑ t ∈ C, inst.c t - 3 * Real.log n * ∑ t : T, w t * inst.c t := by
      rw [Finset.sum_sub_distrib, hsumC, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun t _ => by ring
    have hlog : 0 ≤ Real.log n := Real.log_nonneg hn1
    have h4 : ∑ t ∈ C, inst.c t - 3 * Real.log n * ∑ t : T, w t * inst.c t < 2 * α * Real.log n := by
      have h5 : X * (2 * α) = ∑ t ∈ C, inst.c t - 3 * Real.log n * ∑ t : T, w t * inst.c t := by
        rw [hX, hsplit]; field_simp
      have h6 : X * (2 * α) < Real.log n * (2 * α) := mul_lt_mul_of_pos_right h3 (by linarith)
      linarith
    have h7 : 3 * Real.log n * ∑ t : T, w t * inst.c t ≤ 3 * Real.log n * (β * α) :=
      mul_le_mul_of_nonneg_left hfrac (by linarith)
    nlinarith


theorem wpot_mono (inst : SetCoverInstance X T) (α : ℝ) (σ : List X) {c : Config X T}
    (h : Reachable inst α σ c) : ∀ s, c = .ok s →
    potential inst s.w s.C α ≤ potential inst (initState σ : AlgState X T).w ∅ α := by
  induction h with
  | init => intro s hs; cases hs; exact le_refl _
  | @step s0 c0 hr hst ih =>
    intro s hs
    subst hs
    have IH := ih _ rfl
    cases hst with
    | arrive j rest hcur hpend => exact IH
    | finish j hcur _ => exact IH
    | startStep j l hcur hlt henum => exact IH
    | process j S l w' C' hcur hps =>
      exact le_trans (wps_some inst α _ _ _ _ _ hps).2.2 IH

open Classical in
theorem wpot_init (inst : SetCoverInstance X T) (α : ℝ) (σ : List X)
    (hα : Nonempty T → 0 < α)
    (hsize : (Fintype.card X : ℝ) * (Fintype.card X : ℝ) ^ ((2 : ℝ) / (Fintype.card T : ℝ)) +
        (Fintype.card X : ℝ) < (Fintype.card X : ℝ) ^ 2) :
    potential inst (initState σ : AlgState X T).w ∅ α < (Fintype.card X : ℝ) ^ 2 := by
  have hn1 : (1 : ℝ) ≤ Fintype.card X := by
    by_contra hcon
    push_neg at hcon
    have h0 : (0 : ℝ) ≤ Fintype.card X := by positivity
    have : (Fintype.card X : ℝ) ^ 2 ≤ Fintype.card X := by nlinarith
    have : 0 ≤ (Fintype.card X : ℝ) * (Fintype.card X : ℝ) ^ ((2 : ℝ) / (Fintype.card T : ℝ)) :=
      mul_nonneg h0 (Real.rpow_nonneg h0 _)
    linarith
  have hN : (0 : ℝ) < Fintype.card X := by linarith
  rw [wpot_def]
  have hF : (∑ e, if coveredBy inst ∅ e then (0 : ℝ) else
      (Fintype.card X : ℝ) ^ (2 * elementWeight inst (initState σ : AlgState X T).w e)) ≤
      (Fintype.card X : ℝ) * (Fintype.card X : ℝ) ^ ((2 : ℝ) / (Fintype.card T : ℝ)) := by
    have : ∀ e : X, (if coveredBy inst ∅ e then (0 : ℝ) else
        (Fintype.card X : ℝ) ^ (2 * elementWeight inst (initState σ : AlgState X T).w e)) ≤
        (Fintype.card X : ℝ) ^ ((2 : ℝ) / (Fintype.card T : ℝ)) := by
      intro e
      have hnc : ¬ coveredBy inst ∅ e := fun ⟨t, _, ht⟩ => by simp at ht
      rw [if_neg hnc]
      apply Real.rpow_le_rpow_of_exponent_le hn1
      simp only [elementWeight, initState, Finset.sum_const, nsmul_eq_mul]
      rcases Nat.eq_zero_or_pos (Fintype.card T) with hT | hT
      · haveI : IsEmpty T := Fintype.card_eq_zero_iff.mp hT
        simp [hT]
      · have hm : (1 : ℝ) ≤ Fintype.card T := by exact_mod_cast hT
        have hc : ((inst.elemSets e).card : ℝ) ≤ Fintype.card T := by
          exact_mod_cast Finset.card_le_univ _
        rw [div_eq_mul_one_div 2 (Fintype.card T : ℝ)]
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
    calc _ ≤ ∑ e : X, (Fintype.card X : ℝ) ^ ((2 : ℝ) / (Fintype.card T : ℝ)) :=
          Finset.sum_le_sum fun e _ => this e
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hE : Real.exp ((1 / (2 * α)) * ∑ t : T, (inst.c t * (if t ∈ (∅ : Finset T) then (1 : ℝ) else 0) -
      3 * (initState σ : AlgState X T).w t * inst.c t * Real.log (Fintype.card X : ℝ))) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    rcases isEmpty_or_nonempty T with hT | hT
    · simp
    · have hα0 := hα hT
      apply mul_nonpos_of_nonneg_of_nonpos (by positivity)
      apply Finset.sum_nonpos
      intro t _
      have := Real.log_nonneg hn1
      have := (inst.hc_pos t).le
      simp only [Finset.notMem_empty, if_false, mul_zero, zero_sub, initState, neg_nonpos]
      positivity
  have := mul_le_mul_of_nonneg_left hE hN.le
  linarith

theorem theorem_3_4_core (inst : SetCoverInstance X T) (α : ℝ) (Copt : Finset T) (σ : List X)
    (hc_one : ∀ S, 1 ≤ inst.c S)
    (hc_m : ∀ S, inst.c S ≤ (Fintype.card T : ℝ))
    (hc_α : ∀ S, inst.c S ≤ α)
    (hcov : ∀ j ∈ σ, coveredBy inst Copt j)
    (hopt : ∑ S ∈ Copt, inst.c S ≤ α)
    (hsize : (Fintype.card X : ℝ) * (Fintype.card X : ℝ) ^ ((2 : ℝ) / (Fintype.card T : ℝ)) +
        (Fintype.card X : ℝ) < (Fintype.card X : ℝ) ^ 2)
    (c : Config X T) (hc : Reachable inst α σ c) :
    ∃ s : AlgState X T, c = .ok s ∧
      (∀ j : X, 1 ≤ elementWeight inst s.w j → coveredBy inst s.C j) ∧
      ∑ S ∈ s.C, inst.c S ≤
        3 * Real.log (Fintype.card X : ℝ) *
            (1 + (1 + 1 / (Fintype.card X : ℝ)) * α *
              Real.log ((Fintype.card T : ℝ) ^ 2 * (1 + 1 / (Fintype.card X : ℝ)))) +
          2 * α * Real.log (Fintype.card X : ℝ) := by
  have hα0 : 0 ≤ α := le_trans (Finset.sum_nonneg fun S _ => (inst.hc_pos S).le) hopt
  have hαT : Nonempty T → 0 < α := fun ⟨S⟩ => by linarith [hc_one S, hc_α S]
  have hn1 : (1 : ℝ) ≤ Fintype.card X := by
    by_contra hcon
    push_neg at hcon
    have h0 : (0 : ℝ) ≤ Fintype.card X := by positivity
    have : (Fintype.card X : ℝ) ^ 2 ≤ Fintype.card X := by nlinarith
    have : 0 ≤ (Fintype.card X : ℝ) * (Fintype.card X : ℝ) ^ ((2 : ℝ) / (Fintype.card T : ℝ)) :=
      mul_nonneg h0 (Real.rpow_nonneg h0 _)
    linarith
  have hlog : 0 ≤ Real.log (Fintype.card X : ℝ) := Real.log_nonneg hn1
  rcases c with s | _
  swap
  · exfalso
    rcases isEmpty_or_nonempty T with hT | hT
    · cases hc with
      | @step s0 c0 hr hst =>
        cases hst with
        | processFail j S => exact isEmptyElim S
    · exact (lemma_3_3_core inst α (hαT hT)).2 hc_α σ hc
  refine ⟨s, rfl, ?_⟩
  rcases isEmpty_or_nonempty T with hT | hT
  · refine ⟨fun j hj => ?_, ?_⟩
    · have : inst.elemSets j = ∅ := Finset.eq_empty_of_isEmpty _
      simp [elementWeight, this] at hj
      linarith
    · have : s.C = ∅ := Finset.eq_empty_of_isEmpty _
      rw [this, Finset.sum_empty]
      have := wL0_nonneg (X := X) (T := T)
      have : 0 ≤ (1 + 1 / (Fintype.card X : ℝ)) := by positivity
      positivity
  · have hα := hαT hT
    have hΦ := lt_of_le_of_lt (wpot_mono inst α σ hc s rfl) (wpot_init inst α σ hαT hsize)
    obtain ⟨-, h32⟩ := lemma_3_2_core inst α Copt σ hc_one hc_m hcov hopt s hc
    obtain ⟨I1, -⟩ := winv_reach inst α σ hc s rfl
    set B : ℝ := 1 + (1 + 1 / (Fintype.card X : ℝ)) * α *
        Real.log ((Fintype.card T : ℝ) ^ 2 * (1 + 1 / (Fintype.card X : ℝ))) with hB
    have hB0 : 0 ≤ B := by
      have := wL0_nonneg (X := X) (T := T)
      have : 0 ≤ (1 + 1 / (Fintype.card X : ℝ)) := by positivity
      positivity
    have hfrac : ∑ t : T, s.w t * inst.c t ≤ (B / α) * α := by
      rw [div_mul_cancel₀ _ hα.ne']; exact h32
    obtain ⟨hi, hii⟩ := wopd_main inst α (B / α) hα (by positivity) s.w
      (fun t => le_trans (by positivity) (I1 t)) s.C (by exact_mod_cast hn1) hfrac hΦ
    refine ⟨hi, le_trans hii (le_of_eq ?_)⟩
    field_simp

end OnlineSetCover.Weighted

open OnlineSetCover.Weighted


theorem solution {X T : Type*} [Fintype X] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance X T) (α : ℝ) (Copt : Finset T) (σ : List X)
    (hc_one : ∀ S, 1 ≤ inst.c S)
    (hc_m : ∀ S, inst.c S ≤ (Fintype.card T : ℝ))
    (hc_α : ∀ S, inst.c S ≤ α)
    (hcov : ∀ j ∈ σ, coveredBy inst Copt j)
    (hopt : ∑ S ∈ Copt, inst.c S ≤ α)
    (hsize : (Fintype.card X : ℝ) * (Fintype.card X : ℝ) ^ ((2 : ℝ) / (Fintype.card T : ℝ)) +
        (Fintype.card X : ℝ) < (Fintype.card X : ℝ) ^ 2)
    (c : Config X T) (hc : Reachable inst α σ c) :
    ∃ s : AlgState X T, c = .ok s ∧
      (∀ j : X, 1 ≤ elementWeight inst s.w j → coveredBy inst s.C j) ∧
      ∑ S ∈ s.C, inst.c S ≤
        3 * Real.log (Fintype.card X : ℝ) *
            (1 + (1 + 1 / (Fintype.card X : ℝ)) * α *
              Real.log ((Fintype.card T : ℝ) ^ 2 * (1 + 1 / (Fintype.card X : ℝ)))) +
          2 * α * Real.log (Fintype.card X : ℝ) := by
  exact theorem_3_4_core inst α Copt σ hc_one hc_m hc_α hcov hopt hsize c hc
