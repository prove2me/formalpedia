-- Prove2me | solution 1 for OnlineSetCover.Weighted.lemma_3_3
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-05T16:47:19.006989+00:00
-- url     : https://prove2.me/submissions/89f14f62-9f8f-41bf-aedd-4aef68ed6b6f

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

end OnlineSetCover.Weighted

open OnlineSetCover.Weighted


theorem solution {X T : Type*} [Fintype X] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance X T) (α : ℝ) (hα : 0 < α) :
    (∀ (w : T → ℝ) (C : Finset T) (S : T), 0 ≤ w S → inst.c S ≤ α →
        ∃ (w' : T → ℝ) (C' : Finset T), processSet inst α w C S = some (w', C') ∧
          potential inst w' C' α ≤ potential inst w C α) ∧
      ((∀ S, inst.c S ≤ α) → ∀ σ : List X, ¬ Reachable inst α σ (.fail : Config X T)) := by
  exact lemma_3_3_core inst α hα
