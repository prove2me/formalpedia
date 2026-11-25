-- Prove2me | solution 1 for PI.OmLocU.CntFF.card_diag2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:29:33.577328+00:00
-- url     : https://prove2.me/submissions/d9ff182b-c9b0-41e3-aef9-0eb3885b11b0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensFFIn
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensFFS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalUnitaryOrbits_FFInert2Holds
import Theorems.Thm_PI_OmLocU_CntFF_card_norm2
import Theorems.Thm_PI_VolStabSW_FFHS_finrank_perp
import Theorems.Thm_PI_VolStabSW_FFHS_mem_perp
import Theorems.Thm_PI_VolStabSW_FFHS_perp_isHS


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.OmLocU PI.OmLocU.CntFF
open Module PI.VolStabSW PI.VolStabSW.FFHS
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {σ : K →+* K}
namespace PI.OmLocU.CntFF
theorem _root_.solution (q : ℕ) (hq0 : 0 < q) (hK : Fintype.card K = q ^ 2) (hσ : ∀ x, σ (σ x) = x)
    (h2 : ∃ z : K, z + σ z ≠ 0)
    (hN : ∀ d, σ d = d → Nat.card {t : K // t * σ t = d} = if d = 0 then 1 else q + 1) :
    ∀ (a m : ℕ), a ≤ m → ∀ (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
      (h : V → V → K), IsHS σ h → finrank K V = m → ∀ d : Fin a → K, (∀ i, σ (d i) = d i) →
      (∀ i, d i ≠ 0) →
      (Nat.card {Y : Fin a → V // ∀ i j, h (Y i) (Y j) = if i = j then d i else 0} : ℝ) =
        ∏ j : Fin a, ((q : ℝ) ^ (2 * (m - j) - 1) - (-1) ^ (m - j) * (q : ℝ) ^ (m - j - 1)) := by
  classical
  intro a
  induction a with
  | zero =>
    intro m _ V _ _ _ h hs hm d _ _
    have h1 : Nat.card {Y : Fin 0 → V // ∀ i j, h (Y i) (Y j) = if i = j then d i else 0} = 1 :=
      Nat.card_eq_one_iff_exists.mpr ⟨⟨Fin.elim0, fun i => Fin.elim0 i⟩,
        fun y => Subtype.ext (funext fun i => Fin.elim0 i)⟩
    rw [h1]
    simp
  | succ a ih =>
    intro m ham V _ _ _ h hs hm d hd hd0
    haveI : Finite V := Module.finite_of_finite K
    let e : {Y : Fin (a + 1) → V // ∀ i j, h (Y i) (Y j) = if i = j then d i else 0} ≃
        Σ y : {x : V // h x x = d 0}, {Y' : Fin a → perp hs.toIsSq y.1 //
          ∀ i j, h (Y' i : V) (Y' j) = if i = j then d i.succ else 0} :=
      { toFun := fun Y => ⟨⟨Y.1 0, by simpa using Y.2 0 0⟩,
          ⟨fun i => ⟨Y.1 i.succ, (mem_perp hs.toIsSq _ _).mpr
            (by simpa [(Fin.succ_ne_zero i).symm] using Y.2 0 i.succ)⟩,
           fun i j => by simpa [Fin.succ_inj] using Y.2 i.succ j.succ⟩⟩
        invFun := fun p => ⟨Fin.cons p.1.1 (fun i => (p.2.1 i : V)), fun i j => by
          cases i using Fin.cases with
          | zero =>
            cases j using Fin.cases with
            | zero => simpa using p.1.2
            | succ j =>
              simp only [Fin.cons_zero, Fin.cons_succ]
              rw [if_neg (Fin.succ_ne_zero j).symm]
              exact (mem_perp hs.toIsSq _ _).mp (p.2.1 j).2
          | succ i =>
            cases j using Fin.cases with
            | zero =>
              simp only [Fin.cons_zero, Fin.cons_succ]
              rw [if_neg (Fin.succ_ne_zero i), hs.herm, (mem_perp hs.toIsSq _ _).mp (p.2.1 i).2,
                map_zero]
            | succ j =>
              simp only [Fin.cons_succ]
              rw [p.2.2 i j]
              simp [Fin.succ_inj]⟩
        left_inv := fun Y => by
          apply Subtype.ext
          funext i
          cases i using Fin.cases <;> rfl
        right_inv := fun p => by
          rcases p with ⟨⟨y, hy⟩, ⟨Y', hY'⟩⟩
          rfl }
    haveI : Fintype {x : V // h x x = d 0} := Fintype.ofFinite _
    have hfib : ∀ y : {x : V // h x x = d 0},
        (Nat.card {Y' : Fin a → perp hs.toIsSq y.1 //
          ∀ i j, h (Y' i : V) (Y' j) = if i = j then d i.succ else 0} : ℝ) =
        ∏ j : Fin a, ((q : ℝ) ^ (2 * (m - 1 - j) - 1) - (-1) ^ (m - 1 - j) * (q : ℝ) ^ (m - 1 - j - 1)) :=
      fun y => ih (m - 1) (by omega) (perp hs.toIsSq y.1) (fun w w' => h w w')
        (perp_isHS hs y.1 (by rw [y.2]; exact hd0 0))
        (by have := finrank_perp hs.toIsSq y.1 (by rw [y.2]; exact hd0 0); omega)
        (fun i => d i.succ) (fun i => hd i.succ) (fun i => hd0 i.succ)
    have hS := card_norm2 q hq0 hK hσ h2 hN m V h hs hm (d 0) (hd 0)
    have hfirst : (q : ℝ) ^ (2 * (m : ℤ) - 1) + (-1) ^ m * (q : ℝ) ^ ((m : ℤ) - 1) *
        ((if d 0 = 0 then (q : ℝ) else 0) - 1) =
        (q : ℝ) ^ (2 * (m - ((0 : Fin (a + 1)) : ℕ)) - 1) -
          (-1) ^ (m - ((0 : Fin (a + 1)) : ℕ)) * (q : ℝ) ^ (m - ((0 : Fin (a + 1)) : ℕ) - 1) := by
      rw [if_neg (hd0 0), Fin.val_zero, Nat.sub_zero]
      have e1 : (2 * (m : ℤ) - 1) = ((2 * m - 1 : ℕ) : ℤ) := by omega
      have e2 : ((m : ℤ) - 1) = ((m - 1 : ℕ) : ℤ) := by omega
      rw [e1, e2, zpow_natCast, zpow_natCast]
      ring
    rw [Nat.card_congr e, Nat.card_sigma, Nat.cast_sum, Finset.sum_congr rfl (fun y _ => hfib y),
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card, hS, hfirst,
      Fin.prod_univ_succ]
    congr 1
    refine Finset.prod_congr rfl (fun j _ => ?_)
    rw [Fin.val_succ, show m - (↑j + 1) = m - 1 - ↑j by omega]
end PI.OmLocU.CntFF
