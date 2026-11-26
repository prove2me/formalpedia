-- Prove2me | solution 1 for SmallClassesNeighbourhood.Linear.orbit_stabilizer_bound
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T02:49:32.783091+00:00
-- url     : https://prove2.me/submissions/6d1f67bb-8ea5-4d87-a8a8-ec7985fac46a

import Definitions.Def_SmallClassesNeighbourhood_Linear_groupActions
namespace SmallClassesNeighbourhood.Linear

theorem _root_.solution {H Γ : Type} [Group H] [Fintype H]
    [Fintype Γ] [DecidableEq Γ] [MulAction H Γ] (k : ℕ) (S : Fin k → Finset Γ) :
    Fintype.card H = (tupleOrbit (H := H) S).card * Nat.card (tupleStabilizer (H := H) S) ∧
    Fintype.card H ≤ (2 ^ k) ^ Fintype.card Γ * Nat.card (tupleStabilizer (H := H) S) := by
  classical
  set act : H → (Fin k → Finset Γ) := fun h => fun i => (S i).image (fun x => h • x) with hact
  have horb : SmallClassesNeighbourhood.Linear.tupleOrbit (H := H) S = Finset.univ.image act := by
    unfold SmallClassesNeighbourhood.Linear.tupleOrbit; rfl
  have hmem : ∀ h : H, h ∈ SmallClassesNeighbourhood.Linear.tupleStabilizer (H := H) S ↔ act h = act 1 := by
    intro h
    have h1 : act 1 = S := by funext i; simp [hact]
    rw [h1]
    show (∀ i : Fin k, ∀ x : Γ, h • x ∈ S i ↔ x ∈ S i) ↔ act h = S
    constructor
    · intro hs; funext i; ext y
      simp only [hact, Finset.mem_image]
      constructor
      · rintro ⟨x, hx, rfl⟩; exact (hs i x).2 hx
      · intro hy
        refine ⟨h⁻¹ • y, (hs i _).1 (by rwa [smul_inv_smul]), smul_inv_smul h y⟩
    · intro he i x
      have e : (S i).image (fun x => h • x) = S i := congrFun he i
      constructor
      · intro hx
        rw [← e, Finset.mem_image] at hx
        obtain ⟨z, hz, hzx⟩ := hx
        rwa [← MulAction.injective h hzx]
      · intro hx
        rw [← e]; exact Finset.mem_image_of_mem _ hx
  have hmul : ∀ a b : H, act (a * b) = fun i => (act b i).image (fun x => a • x) := by
    intro a b; funext i
    simp only [hact, Finset.image_image]
    exact Finset.image_congr fun x _ => by simp [Function.comp, mul_smul]
  have hfib : ∀ T ∈ Finset.univ.image act,
      (Finset.univ.filter fun h => act h = T).card = Nat.card (SmallClassesNeighbourhood.Linear.tupleStabilizer (H := H) S) := by
    intro T hT
    obtain ⟨g, _, rfl⟩ := Finset.mem_image.1 hT
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    refine (Finset.card_bij' (fun h _ => g⁻¹ * h) (fun s _ => g * s) ?_ ?_ ?_ ?_)
    · intro h hh
      rw [Finset.mem_filter] at hh ⊢
      refine ⟨Finset.mem_univ _, (hmem _).2 ?_⟩
      rw [hmul, hh.2, ← hmul, inv_mul_cancel]
    · intro s hs
      rw [Finset.mem_filter] at hs ⊢
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [hmul, (hmem _).1 hs.2, ← hmul, mul_one]
    · intro h _; simp
    · intro s _; simp
  have hmain : Fintype.card H = (SmallClassesNeighbourhood.Linear.tupleOrbit (H := H) S).card
      * Nat.card (SmallClassesNeighbourhood.Linear.tupleStabilizer (H := H) S) := by
    rw [horb, ← Finset.card_univ, Finset.card_eq_sum_card_image act, Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul]
  refine ⟨hmain, ?_⟩
  rw [hmain]
  refine Nat.mul_le_mul_right _ (le_trans (Finset.card_le_univ _) (le_of_eq ?_))
  rw [Fintype.card_fun, Fintype.card_finset, Fintype.card_fin, ← pow_mul, ← pow_mul, Nat.mul_comm]


end SmallClassesNeighbourhood.Linear

