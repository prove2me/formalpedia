-- Prove2me | solution 1 for PI.VolStabW.FFHS.card_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:32:42.514365+00:00
-- url     : https://prove2.me/submissions/41f99fb7-41fd-47a7-bf32-357f05a4aa78

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensFFHS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensFFCnt
import Theorems.Thm_PI_VolStabW_FFHS_card_norm
import Theorems.Thm_PI_VolStabW_FFHS_finrank_perp
import Theorems.Thm_PI_VolStabW_FFHS_mem_perp
import Theorems.Thm_PI_VolStabW_FFHS_perp_isHS


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW PI.VolStabW.FFHS
open Module
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {σ : K →+* K}
namespace PI.VolStabW.FFHS
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
    intro m _ V _ _ _ h _ _ d _ _
    have : Nat.card {Y : Fin 0 → V // ∀ i j, h (Y i) (Y j) = if i = j then d i else 0} = 1 :=
      Nat.card_eq_one_iff_exists.2 ⟨⟨Fin.elim0, fun i => i.elim0⟩,
        fun y => Subtype.ext (funext fun i => i.elim0)⟩
    rw [this]
    simp
  | succ a ih =>
    intro m ham V _ _ _ h hs hm d hd hd0
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have hq := hs.toIsSq
    have : Finite V := Module.finite_of_finite K
    have : Fintype V := Fintype.ofFinite V
    classical
    let E : {Y : Fin (a + 1) → V // ∀ i j, h (Y i) (Y j) = if i = j then d i else 0} ≃
        Σ x : {x : V // h x x = d 0}, {Z : Fin a → perp hq x.1 //
          ∀ i j, h (Z i) (Z j) = if i = j then d i.succ else 0} :=
      { toFun := fun Y => ⟨⟨Y.1 0, by simpa using Y.2 0 0⟩,
          ⟨fun i => ⟨Y.1 i.succ, (mem_perp hq _ _).2 (by
            have := Y.2 0 i.succ; rwa [if_neg (Fin.succ_ne_zero i).symm] at this)⟩,
            fun i j => by
              have := Y.2 i.succ j.succ
              simpa only [Fin.succ_inj] using this⟩⟩
        invFun := fun p => ⟨Fin.cons p.1.1 (fun i => (p.2.1 i : V)), by
          intro i j
          induction i using Fin.cases with
          | zero =>
            induction j using Fin.cases with
            | zero => simpa using p.1.2
            | succ j =>
              simp only [Fin.cons_zero, Fin.cons_succ]
              rw [if_neg (Fin.succ_ne_zero j).symm]
              exact (mem_perp hq _ _).1 (p.2.1 j).2
          | succ i =>
            induction j using Fin.cases with
            | zero =>
              simp only [Fin.cons_zero, Fin.cons_succ]
              rw [if_neg (Fin.succ_ne_zero i), hq.herm, (mem_perp hq _ _).1 (p.2.1 i).2,
                map_zero]
            | succ j =>
              simp only [Fin.cons_succ, Fin.succ_inj]
              exact p.2.2 i j⟩
        left_inv := fun Y => Subtype.ext (funext fun i => by
          induction i using Fin.cases with
          | zero => rfl
          | succ i => rfl)
        right_inv := fun p => rfl }
    rw [Nat.card_congr E, Nat.card_sigma, Nat.cast_sum]
    have hfr : ∀ x : {x : V // h x x = d 0}, finrank K (perp hq x.1) = m' := fun x => by
      have := finrank_perp hq x.1 (by rw [x.2]; exact hd0 0); omega
    have hsum : ∀ x : {x : V // h x x = d 0}, (Nat.card {Z : Fin a → perp hq x.1 //
        ∀ i j, h (Z i) (Z j) = if i = j then d i.succ else 0} : ℝ) =
        ∏ j : Fin a, ((q : ℝ) ^ (2 * (m' - j) - 1) - (-1) ^ (m' - j) * (q : ℝ) ^ (m' - j - 1)) :=
      fun x => ih m' (by omega) (perp hq x.1) (fun w w' => h w w')
        (perp_isHS hs x.1 (by rw [x.2]; exact hd0 0)) (hfr x) (fun i => d i.succ)
        (fun i => hd i.succ) (fun i => hd0 i.succ)
    rw [Finset.sum_congr rfl (fun x _ => hsum x)]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card,
      card_norm q hq0 hK hσ h2 hN (m' + 1) V h hs hm (d 0) (hd 0), if_neg (hd0 0),
      Fin.prod_univ_succ]
    congr 1
    · simp only [Fin.val_zero, Nat.sub_zero]
      rw [show 2 * ((m' + 1 : ℕ) : ℤ) - 1 = ((2 * (m' + 1) - 1 : ℕ) : ℤ) by omega,
        show ((m' + 1 : ℕ) : ℤ) - 1 = ((m' + 1 - 1 : ℕ) : ℤ) by omega, zpow_natCast,
        zpow_natCast]
      ring
    · refine Finset.prod_congr rfl (fun j _ => ?_)
      rw [Fin.val_succ, show m' + 1 - (j + 1 : ℕ) = m' - j by omega]
end PI.VolStabW.FFHS
