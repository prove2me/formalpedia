-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P16.noetherian_reconstruction
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T00:03:48.631241+00:00
-- url     : https://prove2.me/submissions/160b8758-12da-4fb0-920d-79636d1afccd

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P16
noncomputable section

universe u

open QAlgorithms.Papers.Independent.Gap48.P16

open scoped TensorProduct

section Pairings

variable {R A P Q B M : Type u} [CommRing R]

variable [AddCommGroup A] [Module R A] [AddCommGroup P] [Module R P]

variable [AddCommGroup Q] [Module R Q] [AddCommGroup B] [Module R B]

variable [AddCommGroup M] [Module R M]

theorem g74b_reconstruct {R : Type u} [CommRing R] [IsNoetherianRing R]
    (S : Type u) (n : ℕ) (f : Fin n → S → R) :
    ∃ (m : ℕ) (s : Fin m → S) (g : Fin m → S → R),
      ∀ i x, f i x = ∑ l, f i (s l) * g l x := by
  classical
  let v : S → (Fin n → R) := fun x i => f i x
  obtain ⟨t, ht, hspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset (R := R)
    (Set.range v)).1 (IsNoetherian.noetherian _)
  have hex : ∀ y : (t : Set (Fin n → R)), ∃ x, v x = y := fun y => ht y.2
  choose s0 hs0 using hex
  let e := t.equivFin
  let s : Fin t.card → S := fun l => s0 ⟨(e.symm l).1, (e.symm l).2⟩
  have hle : Submodule.span R (t : Set (Fin n → R)) ≤
      Submodule.span R (Set.range fun l => v (s l)) := by
    rw [Submodule.span_le]
    intro y hy
    apply Submodule.subset_span
    refine ⟨e ⟨y, hy⟩, ?_⟩
    simp only [s, Equiv.symm_apply_apply]
    exact hs0 ⟨y, hy⟩
  have hx : ∀ x, v x ∈ Submodule.span R (Set.range fun l => v (s l)) := fun x =>
    hle (hspan ▸ Submodule.subset_span ⟨x, rfl⟩)
  have hx' := fun x => (Submodule.mem_span_range_iff_exists_fun R).1 (hx x)
  choose c hc using hx'
  refine ⟨t.card, s, fun l x => c x l, ?_⟩
  intro i x
  have := congrFun (hc x) i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, v] at this
  rw [← this]
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _

/-- Lemma 2.13, PDF pp.7-8: simultaneous finite reconstruction and its corollary. -/
theorem solution [IsNoetherianRing R] :
    (∀ (S : Type u) (n : ℕ) (f : Fin n → S → R),
      ∃ (m : ℕ) (s : Fin m → S) (g : Fin m → S → R),
        ∀ i x, f i x = ∑ l, f i (s l) * g l x) ∧
    (∀ (b : P →ₗ[R] A →ₗ[R] R),
      Function.Injective (pairingAlpha b R) → IsMockProjective b) := by
  refine ⟨fun S n f => g74b_reconstruct S n f, fun b hb => ⟨hb, fun n p => ?_⟩⟩
  obtain ⟨m, a, g, h⟩ := g74b_reconstruct A n (fun i x => b (p i) x)
  exact ⟨m, a, g, h⟩


end Pairings



end
