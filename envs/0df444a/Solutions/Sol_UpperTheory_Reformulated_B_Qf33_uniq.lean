-- Prove2me | solution 1 for UpperTheory.Reformulated.B.Qf33.uniq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:51:58.708881+00:00
-- url     : https://prove2.me/submissions/a02adbd0-e630-438e-8e2d-be46e4041383

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BlockDiagonalLeviEmbedding
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open scoped Classical
private theorem rad_spec {R : Type} [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
    [(a : α) → Fintype (m a)] [(a : α) → DecidableEq (m a)] [Fintype n] [DecidableEq n]
    (e : (a : α) × m a ≃ n) {g : GL n R} (hg : g ∈ UpperTheory.Reformulated.B.Qf33.unipRad R e) :
    (g : Matrix n n R).BlockTriangular (UpperTheory.Reformulated.B.Qf33.blk e) ∧
      ∀ (a : α) (i j : m a), (g : Matrix n n R) (e ⟨a, i⟩) (e ⟨a, j⟩) = (1 : Matrix (m a) (m a) R) i j := by
  obtain ⟨p, hp, rfl⟩ := hg
  refine ⟨p.2, fun a i j ↦ ?_⟩
  have h1 : UpperTheory.Reformulated.B.Qf33.leviProj R e p = 1 := hp
  have h2 := congrArg Units.val (congrFun h1 a)
  exact congrFun (congrFun h2 i) j
private theorem levi_off {R : Type} [CommRing R] {α n : Type} {m : α → Type} [Fintype α]
    [(a : α) → Fintype (m a)] [(a : α) → DecidableEq (m a)] [Fintype n] [DecidableEq n]
    (e : (a : α) × m a ≃ n) {g : GL n R} (hg : g ∈ (UpperTheory.Reformulated.B.Qf33.leviEmb R e).range) {i j : n}
    (hij : UpperTheory.Reformulated.B.Qf33.blk e i ≠ UpperTheory.Reformulated.B.Qf33.blk e j) : (g : Matrix n n R) i j = 0 := by
  obtain ⟨l, rfl⟩ := hg
  exact Matrix.blockDiagonal'_apply_ne (fun (a : α) ↦ (↑(l a) : Matrix (m a) (m a) R))
    (e.symm i).2 (e.symm j).2 hij
private theorem eq_one_of_blocks {R : Type} [CommRing R] {α n : Type} {m : α → Type}
    [(a : α) → DecidableEq (m a)] [Fintype n] [DecidableEq n]
    (e : (a : α) × m a ≃ n) {g : GL n R}
    (h0 : ∀ i j, UpperTheory.Reformulated.B.Qf33.blk e i ≠ UpperTheory.Reformulated.B.Qf33.blk e j → (g : Matrix n n R) i j = 0)
    (h1 : ∀ (a : α) (i j : m a), (g : Matrix n n R) (e ⟨a, i⟩) (e ⟨a, j⟩) = (1 : Matrix (m a) (m a) R) i j) :
    g = 1 := by
  ext i j
  obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective i
  obtain ⟨⟨b, j⟩, rfl⟩ := e.surjective j
  by_cases hab : a = b
  · subst hab
    rw [h1]
    simp [Matrix.one_apply]
  · rw [h0 _ _ (by simpa [UpperTheory.Reformulated.B.Qf33.blk] using hab)]
    simp [Matrix.one_apply, hab]
end

set_option autoImplicit false
open scoped Classical
namespace UpperTheory.Reformulated.B.Qf33
theorem _root_.solution :
    ∀ {R : Type} [inst : CommRing R] {α n : Type} {m : α → Type} [inst_1 : Fintype α] [inst_2 : LinearOrder α]
      [inst_3 : (a : α) → Fintype (m a)] [inst_4 : (a : α) → DecidableEq (m a)] [inst_5 : Fintype n]
      [inst_6 : DecidableEq n] {e : (a : α) × m a ≃ n},
      ∀ a ∈ UpperTheory.Reformulated.B.Qf33.unipRadLower R e,
        ∀ a' ∈ UpperTheory.Reformulated.B.Qf33.unipRadLower R e,
          ∀ b ∈ (UpperTheory.Reformulated.B.Qf33.leviEmb R e).range,
            ∀ b' ∈ (UpperTheory.Reformulated.B.Qf33.leviEmb R e).range,
              ∀ c ∈ UpperTheory.Reformulated.B.Qf33.unipRad R e,
                ∀ c' ∈ UpperTheory.Reformulated.B.Qf33.unipRad R e, a * b * c = a' * b' * c' → a = a' ∧ b = b' ∧ c = c' := by
  intro R _ α n m _ _ _ _ _ _ e a ha a' ha' b hb b' hb' c hc c' hc' h
  have h1 : a'⁻¹ * a = b' * c' * (b * c)⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, eq_mul_inv_iff_mul_eq, ← mul_assoc, ← mul_assoc, h]
  have hP : ∀ x ∈ (UpperTheory.Reformulated.B.Qf33.leviEmb R e).range, x ∈ UpperTheory.Reformulated.B.Qf33.parab R e :=
    fun x hx i j hij ↦ levi_off e hx hij.ne'
  have hU : ∀ x ∈ UpperTheory.Reformulated.B.Qf33.unipRad R e, x ∈ UpperTheory.Reformulated.B.Qf33.parab R e :=
    fun x hx ↦ (rad_spec e hx).1
  have h2 : a'⁻¹ * a ∈ UpperTheory.Reformulated.B.Qf33.parab R e := by
    rw [h1]
    exact mul_mem (mul_mem (hP _ hb') (hU _ hc')) (inv_mem (mul_mem (hP _ hb) (hU _ hc)))
  have h3 : a'⁻¹ * a ∈ UpperTheory.Reformulated.B.Qf33.unipRad R (UpperTheory.Reformulated.B.Qf33.opp e) := mul_mem (inv_mem ha') ha
  have h4 : a'⁻¹ * a = 1 := by
    obtain ⟨ht, hd⟩ := rad_spec _ h3
    refine eq_one_of_blocks e (fun i j hij ↦ ?_) hd
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · exact ht hlt
    · exact h2 hlt
  have haa : a = a' := (inv_mul_eq_one.mp h4).symm
  subst haa
  have h5 : b * c = b' * c' := by
    rw [mul_assoc, mul_assoc] at h
    exact mul_left_cancel h
  have h6 : b'⁻¹ * b = c' * c⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, eq_mul_inv_iff_mul_eq, h5]
  have h7 : b'⁻¹ * b = 1 := by
    refine eq_one_of_blocks e (fun i j hij ↦ levi_off e (mul_mem (inv_mem hb') hb) hij) ?_
    rw [h6]
    exact (rad_spec e (mul_mem hc' (inv_mem hc))).2
  have hbb : b = b' := (inv_mul_eq_one.mp h7).symm
  subst hbb
  exact ⟨rfl, rfl, mul_left_cancel h5⟩
end UpperTheory.Reformulated.B.Qf33
