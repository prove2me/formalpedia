-- Prove2me | solution 1 for PI.VolStabS.FFHS.card_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:27:12.291207+00:00
-- url     : https://prove2.me/submissions/12606cb7-e734-4f6f-b88c-e2e967c07731

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_LocDensFFHS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_LocDensFFCnt
import Theorems.Thm_PI_VolStabS_FFHS_card_norm
import Theorems.Thm_PI_VolStabS_FFHS_finrank_perp
import Theorems.Thm_PI_VolStabS_FFHS_mem_perp
import Theorems.Thm_PI_VolStabS_FFHS_perp_isHS

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace PI.VolStabS.FFHS
open Module
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {σ : K →+* K}
private theorem natCard_sigma_eq_sum {α : Type} [Fintype α] {β : α → Type} [∀ a, Finite (β a)] :
    Nat.card (Sigma β) = ∑ a, Nat.card (β a) := by
  exact Nat.card_sigma
end PI.VolStabS.FFHS
end
end

set_option autoImplicit false
noncomputable section
open PI PI.VolStabS PI.VolStabS.FFHS
open Module
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {σ : K →+* K}
namespace PI.VolStabS.FFHS
theorem _root_.solution (q : ℕ) (hq0 : 0 < q) (hK : Fintype.card K = q ^ 2) (hσ : ∀ x, σ (σ x) = x)
    (h2 : (2 : K) ≠ 0)
    (hN : ∀ d, σ d = d → Nat.card {t : K // t * σ t = d} = if d = 0 then 1 else q + 1) :
    ∀ (a m : ℕ), a ≤ m → ∀ (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
      (h : V → V → K), IsHS σ h → finrank K V = m → ∀ d : Fin a → K, (∀ i, σ (d i) = d i) →
      (∀ i, d i ≠ 0) →
      (Nat.card {Y : Fin a → V // ∀ i j, h (Y i) (Y j) = if i = j then d i else 0} : ℝ) =
        ∏ j : Fin a, ((q : ℝ) ^ (2 * (m - j) - 1) - (-1) ^ (m - j) * (q : ℝ) ^ (m - j - 1)) := by
  intro a
  induction a with
  | zero =>
    intro m _ V i1 i2 i3 h _ _ d _ _
    have : Unique {Y : Fin 0 → V // ∀ i j, h (Y i) (Y j) = if i = j then d i else 0} :=
      ⟨⟨⟨Fin.elim0, fun i => i.elim0⟩⟩, fun Y => Subtype.ext (funext fun i => i.elim0)⟩
    rw [Nat.card_unique, Fin.prod_univ_zero, Nat.cast_one]
  | succ a ih =>
    intro m ham V i1 i2 i3 h hh hm d hd hd0
    have hs := hh.toIsSq
    have : Finite V := Module.finite_of_finite K
    letI : Fintype V := Fintype.ofFinite V
    have hfibEq : ∀ y : V, Nat.card {Z : Fin a → V // (∀ i, h y (Z i) = 0) ∧
          ∀ i j, h (Z i) (Z j) = if i = j then d i.succ else 0} =
        Nat.card {W : Fin a → perp hs y //
          ∀ i j, h (W i) (W j) = if i = j then d i.succ else 0} := by
      intro y
      apply Nat.card_congr
      exact
        { toFun := fun Z => ⟨fun i => ⟨Z.1 i, (mem_perp hs y _).2 (Z.2.1 i)⟩, Z.2.2⟩
          invFun := fun W => ⟨fun i => (W.1 i : V),
            fun i => (mem_perp hs y _).1 (W.1 i).2, W.2⟩
          left_inv := fun Z => rfl
          right_inv := fun W => rfl }
    have hfib : ∀ y : {y : V // h y y = d 0},
        (Nat.card {Z : Fin a → V // (∀ i, h y.1 (Z i) = 0) ∧
          ∀ i j, h (Z i) (Z j) = if i = j then d i.succ else 0} : ℝ) =
          ∏ j : Fin a, ((q : ℝ) ^ (2 * (m - 1 - j) - 1) -
            (-1) ^ (m - 1 - j) * (q : ℝ) ^ (m - 1 - j - 1)) := by
      intro y
      have hy0 : h y.1 y.1 ≠ 0 := by rw [y.2]; exact hd0 0
      rw [hfibEq y.1]
      exact ih (m - 1) (by omega) (perp hs y.1) (fun w w' : perp hs y.1 => h w w')
        (perp_isHS hh y.1 hy0)
        (by have := finrank_perp hs y.1 hy0; omega)
        (fun i => d i.succ) (fun i => hd i.succ) (fun i => hd0 i.succ)
    let E : {Y : Fin (a + 1) → V // ∀ i j, h (Y i) (Y j) = if i = j then d i else 0} ≃
        Σ y : {y : V // h y y = d 0}, {Z : Fin a → V // (∀ i, h y.1 (Z i) = 0) ∧
          ∀ i j, h (Z i) (Z j) = if i = j then d i.succ else 0} :=
      { toFun := fun Y => ⟨⟨Y.1 0, (Y.2 0 0).trans (if_pos rfl)⟩,
          ⟨fun i => Y.1 i.succ, fun i => (Y.2 0 i.succ).trans (if_neg (Fin.succ_ne_zero i).symm),
            fun i j => (Y.2 i.succ j.succ).trans (by simp only [Fin.succ_inj])⟩⟩
        invFun := fun p => ⟨(Fin.cons p.1.1 p.2.1 : Fin (a + 1) → V), by
          intro i j
          induction i using Fin.cases with
          | zero =>
            induction j using Fin.cases with
            | zero => simpa using p.1.2
            | succ j => simpa [(Fin.succ_ne_zero j).symm] using p.2.2.1 j
          | succ i =>
            induction j using Fin.cases with
            | zero =>
              simp only [Fin.cons_zero, Fin.cons_succ]
              rw [if_neg (Fin.succ_ne_zero i), hs.herm, p.2.2.1 i, map_zero]
            | succ j => simpa [Fin.succ_inj] using p.2.2.2 i j⟩
        left_inv := fun Y => Subtype.ext (Fin.cons_self_tail Y.1)
        right_inv := by
          rintro ⟨⟨y, hy⟩, ⟨Z, hZ⟩⟩
          refine Sigma.subtype_ext (Subtype.ext (by simp)) ?_
          funext i
          simp }
    have hN0 : (Nat.card {y : V // h y y = d 0} : ℝ) =
        (q : ℝ) ^ (2 * m - 1) - (-1) ^ m * (q : ℝ) ^ (m - 1) := by
      rw [card_norm q hq0 hK hσ h2 hN m V h hh hm (d 0) (hd 0), if_neg (hd0 0),
        show (2 * (m : ℤ) - 1) = ((2 * m - 1 : ℕ) : ℤ) by omega,
        show ((m : ℤ) - 1) = ((m - 1 : ℕ) : ℤ) by omega, zpow_natCast, zpow_natCast]
      ring
    have hsub : ∀ j : ℕ, m - (j + 1) = m - 1 - j := fun j => by omega
    rw [Nat.card_congr E, natCard_sigma_eq_sum, Nat.cast_sum,
      Finset.sum_congr rfl (fun y _ => hfib y), Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      ← Nat.card_eq_fintype_card, hN0, Fin.prod_univ_succ]
    congr 1
    all_goals first
      | (refine Finset.prod_congr rfl (fun j _ => ?_)
         simp only [Fin.val_succ, hsub j])
      | simp only [Fin.val_zero, Nat.sub_zero]
      | rfl
end PI.VolStabS.FFHS
