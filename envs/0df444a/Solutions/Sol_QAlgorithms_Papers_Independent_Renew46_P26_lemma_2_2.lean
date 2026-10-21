-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P26.lemma_2_2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T00:14:55.934918+00:00
-- url     : https://prove2.me/submissions/eb614e28-bd9e-4ffa-92e0-830d1d9d9b02

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P26
noncomputable section

open scoped BigOperators

open QAlgorithms.Papers.Independent.Renew46.P26

attribute [local instance] Classical.propDecidable

open Equiv

theorem g64f_cycle_refl {α : Type*} [Fintype α] [DecidableEq α] (c : Perm α) (hc : c.IsCycle)
    (b : α) (hb : c b ≠ b) :
    ∃ H : Perm α, H * c = c⁻¹ * H ∧ H b = b ∧ ∀ x, c x = x → H x = x := by
  obtain ⟨σ, hσ⟩ := isConj_iff.mp (Perm.isConj_iff_cycleType_eq.mpr (Perm.cycleType_inv c).symm)
  have hσc : σ * c = c⁻¹ * σ := by rw [← hσ]; group
  have hσx : ∀ x, σ (c x) = c⁻¹ (σ x) := fun x => by
    rw [← Perm.mul_apply, hσc, Perm.mul_apply]
  have hp : ∀ x, (fun y => c y ≠ y) (σ x) ↔ (fun y => c y ≠ y) x := by
    intro x
    simp only [ne_eq]
    constructor
    · intro h1 h2; apply h1
      have : c⁻¹ (σ x) = σ x := by rw [← hσx, h2]
      rw [Perm.inv_eq_iff_eq] at this; exact this.symm
    · intro h1 h2; apply h1
      have : σ (c x) = σ x := by rw [hσx, Perm.inv_eq_iff_eq]; exact h2.symm
      exact σ.injective this
  set H0 := Perm.ofSubtype (σ.subtypePerm (p := fun y => c y ≠ y) hp) with hH0
  have hH0in : ∀ x, c x ≠ x → H0 x = σ x := fun x hx => by
    rw [hH0]; erw [Perm.ofSubtype_apply_of_mem (p := fun y => c y ≠ y) (σ.subtypePerm hp) hx]; rfl
  have hH0out : ∀ x, c x = x → H0 x = x := fun x hx => by
    rw [hH0]; erw [Perm.ofSubtype_apply_of_not_mem _ (by simpa using hx)]
  have hH0c : H0 * c = c⁻¹ * H0 := by
    ext x : 1
    simp only [Perm.mul_apply]
    by_cases hx : c x = x
    · rw [hx, hH0out x hx, eq_comm, Perm.inv_eq_iff_eq, hx]
    · have hcx : c (c x) ≠ c x := fun h => hx (c.injective h)
      rw [hH0in _ hcx, hH0in _ hx, hσx]
  obtain ⟨m, hm⟩ := hc.exists_pow_eq hb ((hp b).mpr hb)
  refine ⟨(c ^ m)⁻¹ * H0, ?_, ?_, ?_⟩
  · rw [mul_assoc, hH0c, ← mul_assoc, ← mul_assoc]
    congr 1
    rw [← mul_inv_rev, ← mul_inv_rev, ← pow_succ, ← pow_succ']
  · rw [Perm.mul_apply, hH0in b hb, ← hm, ← Perm.mul_apply, inv_mul_cancel, Perm.one_apply]
  · intro x hx
    rw [Perm.mul_apply, hH0out x hx, Perm.inv_eq_iff_eq]
    exact (Perm.pow_apply_eq_self_of_apply_eq_self hx m).symm

theorem g64f_refl {α : Type*} [Fintype α] [DecidableEq α] (a : α) (g : Perm α) :
    ∃ H : Perm α, H * g = g⁻¹ * H ∧ H a = a ∧ ∀ x, g x = x → H x = x := by
  induction g using Perm.cycle_induction_on with
  | base_one => exact ⟨1, by simp, rfl, fun _ _ => rfl⟩
  | base_cycles c hc =>
    by_cases ha : c a = a
    · obtain ⟨b, hb, -⟩ := id hc
      obtain ⟨H, h1, _, h3⟩ := g64f_cycle_refl c hc b hb
      exact ⟨H, h1, h3 a ha, h3⟩
    · exact g64f_cycle_refl c hc a ha
  | induction_disjoint σ τ hd _ hσ hτ =>
    obtain ⟨Hs, hs1, hs2, hs3⟩ := hσ
    obtain ⟨Ht, ht1, ht2, ht3⟩ := hτ
    have d1 : Perm.Disjoint Ht σ := fun x => by
      rcases hd x with h | h
      · exact Or.inr h
      · exact Or.inl (ht3 x h)
    have d2 : Perm.Disjoint Hs τ := fun x => by
      rcases hd x with h | h
      · exact Or.inl (hs3 x h)
      · exact Or.inr h
    refine ⟨Hs * Ht, ?_, ?_, ?_⟩
    · have c1 : Ht * σ = σ * Ht := d1.commute
      have c2 : Hs * τ⁻¹ = τ⁻¹ * Hs := (d2.inv_right).commute
      have c3 : σ⁻¹ * τ⁻¹ = τ⁻¹ * σ⁻¹ := (hd.inv_left.inv_right).commute
      calc Hs * Ht * (σ * τ) = Hs * (Ht * σ) * τ := by group
        _ = Hs * σ * (Ht * τ) := by rw [c1]; group
        _ = Hs * σ * (τ⁻¹ * Ht) := by rw [ht1]
        _ = (Hs * σ) * τ⁻¹ * Ht := by group
        _ = σ⁻¹ * (Hs * τ⁻¹) * Ht := by rw [hs1]; group
        _ = σ⁻¹ * τ⁻¹ * Hs * Ht := by rw [c2]; group
        _ = (σ * τ)⁻¹ * (Hs * Ht) := by rw [c3]; group
    · rw [Perm.mul_apply, ht2, hs2]
    · intro x hx
      rw [hd.mul_apply_eq_iff] at hx
      rw [Perm.mul_apply, ht3 x hx.2, hs3 x hx.1]

theorem g64f_pc_via (n : ℕ) (g : Equiv.Perm (Fin n)) :
    Equiv.permCongr finSuccEquivLast (g.viaEmbedding (prefixEmbedding (Nat.le_succ n))) =
      Equiv.optionCongr g := by
  ext x : 1
  rcases x with _ | i
  · simp [Equiv.permCongr_apply]
    rw [Equiv.Perm.viaEmbedding_apply_of_notMem]
    · simp
    · rintro ⟨j, hj⟩
      have := congrArg Fin.val hj
      have h2 : ((prefixEmbedding (Nat.le_succ n)) j).val = j.val := rfl
      rw [h2, Fin.val_last] at this
      exact absurd this (by have := j.isLt; omega)
  · simp [Equiv.permCongr_apply]
    have hc : ∀ j : Fin n, Fin.castSucc j = prefixEmbedding (Nat.le_succ n) j := fun j => Fin.ext rfl
    rw [hc, Equiv.Perm.viaEmbedding_apply, ← hc]
    simp

theorem g64f_oc_rn {β : Type*} (e : Perm (Option β)) (he : e none = none) :
    Equiv.optionCongr (Equiv.removeNone e) = e := by
  ext x : 1
  rcases x with _ | x
  · show none = e none
    rw [he]
  · rcases h : e (some x) with _ | y
    · rw [← he] at h; exact absurd (e.injective h) (by simp)
    · have := Equiv.removeNone_some e ⟨y, h⟩
      rw [h] at this
      show some (Equiv.removeNone e x) = some y
      rw [this]

theorem solution (n : ℕ) (g : Equiv.Perm (Fin (n + 1))) :
    ∃ h : Equiv.Perm (Fin n),
      g⁻¹ = (h.viaEmbedding (prefixEmbedding (Nat.le_succ n))) * g *
        (h.viaEmbedding (prefixEmbedding (Nat.le_succ n)))⁻¹ := by
  obtain ⟨H, hH, hla, -⟩ := g64f_refl (Fin.last n) g
  set e := Equiv.permCongr finSuccEquivLast H with he
  have hen : e none = none := by
    simp [he, Equiv.permCongr_apply, hla]
  refine ⟨Equiv.removeNone e, ?_⟩
  have hv : Equiv.Perm.viaEmbedding (Equiv.removeNone e) (prefixEmbedding (Nat.le_succ n)) = H := by
    apply (Equiv.permCongr finSuccEquivLast).injective
    rw [g64f_pc_via, g64f_oc_rn e hen]
  rw [hv, hH]; group
