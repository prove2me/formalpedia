-- Prove2me | solution 1 for PI.VolStabSW.FFHS.card_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:25:41.863462+00:00
-- url     : https://prove2.me/submissions/dc556a23-ef99-4ab9-87a6-9716216b2142

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensFFHS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensFFCnt
import Theorems.Thm_PI_VolStabSW_FFHS_card_norm
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
open PI PI.VolStabSW PI.VolStabSW.FFHS
open Module
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {σ : K →+* K}
namespace PI.VolStabSW.FFHS
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
    intro m _ V _ _ _ h hh hm d hd hd0
    rw [Fin.prod_univ_zero]
    have h1 : Nat.card {Y : Fin 0 → V // ∀ i j, h (Y i) (Y j) = if i = j then d i else 0} = 1 :=
      Nat.card_eq_one_iff_exists.2
        ⟨⟨Fin.elim0, fun i => Fin.elim0 i⟩, fun Y => Subtype.ext (funext fun i => Fin.elim0 i)⟩
    rw [h1]
    simp
  | succ a ih =>
    intro m ham V _ _ _ h hh hm d hd hd0
    classical
    haveI : Finite V := Module.finite_of_finite K
    haveI := Fintype.ofFinite V
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    let eqv : {Y : Fin (a + 1) → V // ∀ i j, h (Y i) (Y j) = if i = j then d i else 0} ≃
        Σ y0 : {x : V // h x x = d 0}, {Y' : Fin a → perp hh.toIsSq y0.1 //
          ∀ i j, h (Y' i : V) (Y' j : V) = if i = j then d i.succ else 0} :=
      { toFun := fun Y => ⟨⟨Y.1 0, by simpa using Y.2 0 0⟩, ⟨fun i => ⟨Y.1 i.succ, by
            rw [mem_perp]
            have h3 := Y.2 0 i.succ
            rwa [if_neg (Fin.succ_ne_zero i).symm] at h3⟩,
          fun i j => by
            have h3 := Y.2 i.succ j.succ
            simpa [Fin.succ_inj] using h3⟩⟩
        invFun := fun p => ⟨Fin.cons p.1.1 (fun i => (p.2.1 i : V)), by
          intro i j
          refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
          · simpa using p.1.2
          · simp only [Fin.cons_zero, Fin.cons_succ]
            rw [if_neg (Fin.succ_ne_zero j).symm]
            exact (mem_perp _ _ _).1 (p.2.1 j).2
          · simp only [Fin.cons_zero, Fin.cons_succ]
            rw [if_neg (Fin.succ_ne_zero i), hh.toIsSq.herm p.1.1 (p.2.1 i),
              (mem_perp _ _ _).1 (p.2.1 i).2, map_zero]
          · simp only [Fin.cons_succ, Fin.succ_inj]
            exact p.2.2 i j⟩
        left_inv := fun Y => Subtype.ext (Fin.cons_self_tail Y.1)
        right_inv := fun p => rfl }
    rw [Nat.card_congr eqv, Nat.card_sigma, Nat.cast_sum]
    have hfib : ∀ y0 : {x : V // h x x = d 0}, (Nat.card {Y' : Fin a → perp hh.toIsSq y0.1 //
          ∀ i j, h (Y' i : V) (Y' j : V) = if i = j then d i.succ else 0} : ℝ) =
        ∏ j : Fin a, ((q:ℝ) ^ (2 * (m' - j) - 1) - (-1) ^ (m' - j) * (q:ℝ) ^ (m' - j - 1)) := by
      intro y0
      have hy0 : h y0.1 y0.1 ≠ 0 := by rw [y0.2]; exact hd0 0
      have hfr : finrank K (perp hh.toIsSq y0.1) = m' := by
        have := finrank_perp hh.toIsSq y0.1 hy0
        omega
      exact ih m' (by omega) (perp hh.toIsSq y0.1) (fun w w' => h w w') (perp_isHS hh y0.1 hy0) hfr
        (fun i => d i.succ) (fun i => hd i.succ) (fun i => hd0 i.succ)
    rw [Finset.sum_congr rfl (fun y0 _ => hfib y0), Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hN0 := card_norm q hq0 hK hσ h2 hN (m' + 1) V h hh hm (d 0) (hd 0)
    rw [← Nat.card_eq_fintype_card, hN0, if_neg (hd0 0), Fin.prod_univ_succ]
    have z1 : (q:ℝ) ^ (2 * ((m' + 1 : ℕ) : ℤ) - 1) = (q:ℝ) ^ (2 * (m' + 1 - ((0 : Fin (a + 1)) : ℕ)) - 1) := by
      rw [← zpow_natCast]
      congr 1
      simp only [Fin.val_zero]
      omega
    have z2 : (q:ℝ) ^ (((m' + 1 : ℕ) : ℤ) - 1) = (q:ℝ) ^ (m' + 1 - ((0 : Fin (a + 1)) : ℕ) - 1) := by
      rw [← zpow_natCast]
      congr 1
      simp only [Fin.val_zero]
      omega
    rw [z1, z2]
    have hP : ∏ j : Fin a, ((q:ℝ) ^ (2 * (m' + 1 - (j.succ : ℕ)) - 1) -
        (-1) ^ (m' + 1 - (j.succ : ℕ)) * (q:ℝ) ^ (m' + 1 - (j.succ : ℕ) - 1)) =
        ∏ j : Fin a, ((q:ℝ) ^ (2 * (m' - j) - 1) - (-1) ^ (m' - j) * (q:ℝ) ^ (m' - j - 1)) := by
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [Fin.val_succ, Nat.add_sub_add_right]
    rw [hP]
    simp only [Fin.val_zero, Nat.sub_zero]
    ring
end PI.VolStabSW.FFHS
