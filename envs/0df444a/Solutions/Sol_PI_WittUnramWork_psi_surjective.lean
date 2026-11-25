-- Prove2me | solution 1 for PI.WittUnramWork.psi_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:32:52.648445+00:00
-- url     : https://prove2.me/submissions/bd65cb15-c220-43ab-bc5b-aeae2648c097

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WittUnram
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WittUnramified_PsiStep
import Theorems.Thm_PI_WittUnramWork_psi_step

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WittUnramWork
open WittVector Finset
variable {p : ℕ} [hp : Fact p.Prime] {W k : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
  [Field k] [CharP k p] [PerfectRing k p]
namespace PI.WittUnramWork
theorem _root_.solution (ψ : W →+* WittVector p k) (res : W →+* k) (hres : Function.Surjective res)
    (h0 : ∀ x, (ψ x).coeff 0 = res x) (hC : IsAdicComplete (Ideal.span {(p : W)}) W) :
    Function.Surjective ψ := by
  intro w
  choose A B hAB using psi_step ψ res hres h0
  obtain ⟨r, hr0, hrs⟩ : ∃ r : ℕ → WittVector p k, r 0 = w ∧ ∀ n, r (n + 1) = B (r n) :=
    ⟨fun n => B^[n] w, rfl, fun n => Function.iterate_succ_apply' B n w⟩
  obtain ⟨s, hs0, hss⟩ : ∃ s : ℕ → W, s 0 = 0 ∧ ∀ n, s (n + 1) = s n + A (r n) * (p : W) ^ n :=
    ⟨fun n => ∑ i ∈ Finset.range n, A (r i) * (p : W) ^ i, by simp, fun n => Finset.sum_range_succ _ _⟩
  have hinv : ∀ n, w = ψ (s n) + (p : WittVector p k) ^ n * r n := by
    intro n
    induction n with
    | zero => rw [hs0, hr0, map_zero, pow_zero, one_mul, zero_add]
    | succ n ih =>
      calc w = ψ (s n) + (p : WittVector p k) ^ n * r n := ih
        _ = ψ (s n) + (p : WittVector p k) ^ n * (ψ (A (r n)) + (p : WittVector p k) * B (r n)) := by
          rw [← hAB (r n)]
        _ = ψ (s (n + 1)) + (p : WittVector p k) ^ (n + 1) * r (n + 1) := by
          rw [hss, hrs, map_add, map_mul, map_pow, map_natCast]
          ring
  have hdiv : ∀ m n, m ≤ n → (p : W) ^ m ∣ s n - s m := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      rw [hss, add_sub_right_comm]
      exact dvd_add ih (Dvd.dvd.mul_left (pow_dvd_pow _ hmn) _)
  have hI : ∀ n (x : W), x ∈ (Ideal.span {(p : W)} ^ n • ⊤ : Submodule W W) ↔ (p : W) ^ n ∣ x := by
    intro n x
    rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  obtain ⟨L, hL⟩ := hC.toIsPrecomplete.prec (f := s) (fun {m n} hmn => by
    rw [SModEq.sub_mem, hI]
    exact dvd_sub_comm.mp (hdiv m n hmn))
  have hw : ∀ n, (p : WittVector p k) ^ n ∣ w - ψ L := by
    intro n
    obtain ⟨c, hc⟩ := (hI n _).1 (SModEq.sub_mem.1 (hL n))
    refine ⟨ψ c + r n, ?_⟩
    have h2 : ψ (s n) - ψ L = (p : WittVector p k) ^ n * ψ c := by
      rw [← map_sub, hc, map_mul, map_pow, map_natCast]
    calc w - ψ L = ψ (s n) + (p : WittVector p k) ^ n * r n - ψ L := by rw [← hinv n]
      _ = (p : WittVector p k) ^ n * (ψ c + r n) := by linear_combination h2
  have hzero : w - ψ L = 0 := by
    by_contra hne
    obtain ⟨m, b, hb0, hb⟩ := WittVector.exists_eq_pow_p_mul (w - ψ L) hne
    obtain ⟨c, hc⟩ := hw (m + 1)
    rw [hb, pow_succ, mul_assoc] at hc
    have hp : (p : WittVector p k) ^ m ≠ 0 := pow_ne_zero m (WittVector.p_nonzero p k)
    have hbc := mul_left_cancel₀ hp hc
    apply hb0
    rw [hbc]
    first
    | rw [WittVector.mul_coeff_zero, WittVector.coeff_p_zero, zero_mul]
    | simp
  exact ⟨L, (sub_eq_zero.mp hzero).symm⟩
end PI.WittUnramWork
