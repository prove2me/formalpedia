-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P21.band_classIdeal_complement
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T00:00:44.447989+00:00
-- url     : https://prove2.me/submissions/59c431c6-dfaa-4db2-bd5b-1e81c3527689

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P21
open QAlgorithms.Papers.Independent.Renew46.P21

universe u v w

theorem g64j_band_l1 {M : Type*} [Monoid M] (hb : ∀ x : M, x * x = x) (a s b : M) :
    a * s * b * s * (a * s * b) = a * s * b := by
  calc a * s * b * s * (a * s * b) = (a * s) * (a * s) * b * s * (a * s * b) := by rw [hb (a * s)]
    _ = a * ((s * a * s * b) * (s * a * s * b)) := by simp only [mul_assoc]
    _ = a * (s * a * s * b) := by rw [hb]
    _ = (a * s) * (a * s) * b := by simp only [mul_assoc]
    _ = a * s * b := by rw [hb]

theorem g64j_band_l2 {M : Type*} [Monoid M] (hb : ∀ x : M, x * x = x) (r s t : M)
    (hs : r * s * r = r) (ht : r * t * r = r) :
    r = (r * t * r) * (s * t) * (r * s * r) := by
  have h0 : r * t * (r * s * r) = r := by rw [hs, ht]
  calc r = r * t * (r * s * r) := h0.symm
    _ = r * ((t * r * s) * (t * r * s)) * r := by rw [hb]; simp only [mul_assoc]
    _ = (r * t * r) * (s * t) * (r * s * r) := by simp only [mul_assoc]

theorem solution {S : Type v} [Semigroup S]
    (hband : ∀ s : S, s * s = s) (J : JClass S) :
    ∃ T : Subsemigroup S, (T : Set S) = (classIdeal J)ᶜ := by
  have hb : ∀ x : WithOne S, x * x = x := by
    intro x
    rcases x with _ | y
    · rfl
    · show ((y : WithOne S) * (y : WithOne S)) = (y : WithOne S)
      rw [← WithOne.coe_mul, hband]
  have key : ∀ x s t : S, x ∈ principalIdeal s → x ∈ principalIdeal t →
      x ∈ principalIdeal (s * t) := by
    intro x s t ⟨a, b, hab⟩ ⟨c, d, hcd⟩
    have hs : (x : WithOne S) * s * x = x := by rw [hab]; exact g64j_band_l1 hb a _ b
    have ht : (x : WithOne S) * t * x = x := by rw [hcd]; exact g64j_band_l1 hb c _ d
    refine ⟨(x : WithOne S) * t * x, (x : WithOne S) * s * x, ?_⟩
    rw [WithOne.coe_mul]
    exact g64j_band_l2 hb _ _ _ hs ht
  refine ⟨{ carrier := (classIdeal J)ᶜ, mul_mem' := ?_ }, rfl⟩
  intro s t hs ht
  simp only [Set.mem_compl_iff, classIdeal, Set.mem_setOf_eq, not_not] at hs ht ⊢
  intro x hx
  exact key x s t (hs hx) (ht hx)
