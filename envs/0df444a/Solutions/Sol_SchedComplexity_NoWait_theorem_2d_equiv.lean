-- Prove2me | solution 1 for SchedComplexity.NoWait.theorem_2d_equiv
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T12:03:24.891842+00:00
-- url     : https://prove2.me/submissions/ddfd8b89-ec49-43fd-b746-5045665d8e18

import Mathlib
import Definitions.Def_SchedComplexity_NoWait_DirectedGraphs
import Definitions.Def_SchedComplexity_NoWait_Construction



namespace SchedComplexity.NoWait

section hc
variable {N : ℕ} (adj' : Fin (N+1) → Fin (N+1) → Bool) (v' : Fin (N+1))

theorem hc_to_hp (σ : Fin (N+1) ≃ Fin (N+1))
    (hσ : ∀ i, adj' (σ i) (σ (finRotate (N+1) i)) = true) :
    HasHamiltonPath (hcToHpGraph adj' v') := by
  set c := σ.symm v' with hc
  set σ' : Fin (N+1) → Fin (N+1) := fun i => σ (i + c) with hσ'def
  have hσ'inj : Function.Injective σ' := by
    intro a b h
    have := σ.injective h
    exact add_right_cancel this
  have hσ' : ∀ i : Fin (N+1), adj' (σ' i) (σ' (i+1)) = true := by
    intro i
    have := hσ (i + c)
    rw [finRotate_succ_apply] at this
    simp only [hσ'def]
    rw [add_right_comm]
    exact this
  have hσ'0 : σ' 0 = v' := by
    simp [hσ'def, hc]
  let τf : Fin (N+2) → Fin (N+2) := fun k =>
    if h : k.val < N + 1 then Fin.castSucc (σ' ⟨k.val, h⟩) else Fin.last (N+1)
  have hinj : Function.Injective τf := by
    intro a b h
    simp only [τf] at h
    by_cases ha : a.val < N + 1 <;> by_cases hb : b.val < N + 1
    · rw [dif_pos ha, dif_pos hb] at h
      have := hσ'inj (Fin.castSucc_injective _ h)
      exact Fin.ext (by simpa using congrArg Fin.val this)
    · rw [dif_pos ha, dif_neg hb] at h
      exact absurd h (Fin.castSucc_lt_last _).ne
    · rw [dif_neg ha, dif_pos hb] at h
      exact absurd h (Fin.castSucc_lt_last _).ne.symm
    · apply Fin.ext
      have := a.isLt
      have := b.isLt
      omega
  have hbij : Function.Bijective τf := Finite.injective_iff_bijective.mp hinj
  refine ⟨Equiv.ofBijective τf hbij, ?_⟩
  intro i h
  simp only [Equiv.ofBijective_apply, τf]
  by_cases h1 : i.val + 1 < N + 1
  · rw [dif_pos (by omega), dif_pos h1]
    have e : (⟨i.val + 1, h1⟩ : Fin (N+1)) = (⟨i.val, by omega⟩ : Fin (N+1)) + 1 := by
      have hlt : (⟨i.val, by omega⟩ : Fin (N+1)) < Fin.last N := by
        simp only [Fin.lt_def, Fin.val_last]; omega
      exact Fin.ext (by rw [Fin.val_add_one_of_lt hlt])
    unfold hcToHpGraph
    rw [dif_neg (Fin.castSucc_lt_last _).ne, dif_neg (Fin.castSucc_lt_last _).ne]
    have hne : σ' ⟨i.val + 1, h1⟩ ≠ v' := by
      rw [← hσ'0]
      intro hh
      have := congrArg Fin.val (hσ'inj hh)
      simp only [Fin.val_zero] at this
      omega
    rw [e] at hne ⊢
    have := hσ' ⟨i.val, by omega⟩
    simp [this, hne]
  · have hi : i.val = N := by omega
    rw [dif_pos (by omega), dif_neg (by show ¬ (i.val + 1 < N + 1); omega)]
    have e : (⟨i.val, by omega⟩ : Fin (N+1)) + 1 = 0 := by
      have : (⟨i.val, by omega⟩ : Fin (N+1)) = Fin.last N := Fin.ext (by show i.val = N; exact hi)
      rw [this, Fin.last_add_one]
    unfold hcToHpGraph
    rw [dif_neg (Fin.castSucc_lt_last _).ne, dif_pos rfl]
    have := hσ' ⟨i.val, by omega⟩
    rw [e, hσ'0] at this
    simpa using this


theorem G_from_last (b : Fin (N+2)) : hcToHpGraph adj' v' (Fin.last (N+1)) b = false := by
  unfold hcToHpGraph; simp

theorem G_to_v (a : Fin (N+2)) : hcToHpGraph adj' v' a (Fin.castSucc v') = false := by
  unfold hcToHpGraph
  by_cases ha : a = Fin.last (N+1)
  · simp [ha]
  · rw [dif_neg ha, dif_neg (Fin.castSucc_lt_last _).ne]
    simp

theorem G_arc (a b : Fin (N+2)) (ha : a ≠ Fin.last (N+1)) (hb : b ≠ Fin.last (N+1))
    (h : hcToHpGraph adj' v' a b = true) : adj' (a.castPred ha) (b.castPred hb) = true := by
  unfold hcToHpGraph at h
  rw [dif_neg ha, dif_neg hb] at h
  simp only [Bool.and_eq_true] at h
  exact h.1

theorem G_last_arc (a : Fin (N+2)) (ha : a ≠ Fin.last (N+1))
    (h : hcToHpGraph adj' v' a (Fin.last (N+1)) = true) : adj' (a.castPred ha) v' = true := by
  unfold hcToHpGraph at h
  rw [dif_neg ha, dif_pos rfl] at h
  exact h

theorem hp_to_hc (τ : Fin (N+2) ≃ Fin (N+2))
    (hτ : ∀ (i : Fin (N+2)) (h : i.val + 1 < N + 2),
      hcToHpGraph adj' v' (τ i) (τ ⟨i.val + 1, h⟩) = true) :
    HasHamiltonCircuit adj' := by
  have hlast : τ (Fin.last (N+1)) = Fin.last (N+1) := by
    set i := τ.symm (Fin.last (N+1)) with hi
    have hτi : τ i = Fin.last (N+1) := by simp [hi]
    have hl : i = Fin.last (N+1) := by
      by_contra hl
      exfalso
      have hlt : i.val + 1 < N + 2 := by
        have := i.isLt
        have h2 : i.val ≠ N + 1 := fun h => hl (Fin.ext (by simpa using h))
        omega
      have := hτ i hlt
      rw [hτi, G_from_last] at this
      exact Bool.false_ne_true this
    rw [hl] at hτi
    exact hτi
  have hne : ∀ k : Fin (N+1), τ (Fin.castSucc k) ≠ Fin.last (N+1) := by
    intro k h
    rw [← hlast] at h
    have := τ.injective h
    exact (Fin.castSucc_lt_last k).ne this
  have hzero : τ 0 = Fin.castSucc v' := by
    set j := τ.symm (Fin.castSucc v') with hj
    have hτj : τ j = Fin.castSucc v' := by simp [hj]
    have hj0 : j = 0 := by
      by_contra hj0
      exfalso
      have hjpos : 0 < j.val := by
        rcases Nat.eq_zero_or_pos j.val with h | h
        · exact absurd (Fin.ext (by simpa using h)) hj0
        · exact h
      have := hτ ⟨j.val - 1, by have := j.isLt; omega⟩ (show j.val - 1 + 1 < N + 2 by have := j.isLt; omega)
      have e : (⟨j.val - 1 + 1, by have := j.isLt; omega⟩ : Fin (N+2)) = j :=
        Fin.ext (show j.val - 1 + 1 = j.val by omega)
      rw [e, hτj, G_to_v] at this
      exact Bool.false_ne_true this
    rw [hj0] at hτj
    exact hτj
  let σf : Fin (N+1) → Fin (N+1) := fun k => (τ (Fin.castSucc k)).castPred (hne k)
  have hinj : Function.Injective σf := by
    intro a b h
    have : τ (Fin.castSucc a) = τ (Fin.castSucc b) := by
      have := congrArg Fin.castSucc h
      simpa [σf] using this
    exact Fin.castSucc_injective _ (τ.injective this)
  have hbij : Function.Bijective σf := Finite.injective_iff_bijective.mp hinj
  refine ⟨Equiv.ofBijective σf hbij, ?_⟩
  intro i
  simp only [Equiv.ofBijective_apply]
  rw [finRotate_succ_apply]
  by_cases hi : i = Fin.last N
  · subst hi
    rw [Fin.last_add_one]
    have h1 := hτ ⟨N, by omega⟩ (show N + 1 < N + 2 by omega)
    have e1 : (⟨N, by omega⟩ : Fin (N+2)) = Fin.castSucc (Fin.last N) := rfl
    have e2 : (⟨N + 1, by omega⟩ : Fin (N+2)) = Fin.last (N+1) := rfl
    rw [e2, hlast, e1] at h1
    have := G_last_arc adj' v' _ (hne (Fin.last N)) h1
    have e3 : σf 0 = v' := by
      simp only [σf]
      apply Fin.castSucc_injective
      rw [Fin.castSucc_castPred]
      exact hzero
    rw [e3]
    exact this
  · have hlt : i.val + 1 < N + 2 := by
      have := i.isLt
      have h2 : i.val ≠ N := fun h => hi (Fin.ext (by simpa using h))
      omega
    have h1 := hτ (Fin.castSucc i) (by simp; omega)
    have e : (⟨(Fin.castSucc i).val + 1, by simp; omega⟩ : Fin (N+2)) = Fin.castSucc (i + 1) := by
      apply Fin.ext
      simp only [Fin.coe_castSucc]
      rw [Fin.val_add_one_of_lt]
      simp only [Fin.lt_def, Fin.val_last]
      have := i.isLt
      have h2 : i.val ≠ N := fun h => hi (Fin.ext (by simpa using h))
      omega
    rw [e] at h1
    exact G_arc adj' v' _ _ (hne i) (hne (i+1)) h1

end hc

theorem thm2d_core {n : ℕ} (adj' : Fin n → Fin n → Bool) (v' : Fin n) :
    HasHamiltonCircuit adj' ↔ HasHamiltonPath (hcToHpGraph adj' v') := by
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    exact ⟨fun _ => ⟨Equiv.refl _, fun i h => by omega⟩, fun _ => ⟨Equiv.refl _, fun i => i.elim0⟩⟩
  · obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
    constructor
    · rintro ⟨σ, hσ⟩
      exact hc_to_hp adj' v' σ hσ
    · rintro ⟨τ, hτ⟩
      exact hp_to_hc adj' v' τ hτ

end SchedComplexity.NoWait

open SchedComplexity.NoWait


theorem solution {n : ℕ} (adj' : Fin n → Fin n → Bool) (v' : Fin n) :
    HasHamiltonCircuit adj' ↔ HasHamiltonPath (hcToHpGraph adj' v') := by
  exact thm2d_core adj' v'
