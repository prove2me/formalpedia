-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__NZ_exists_labels_77c94fa8b886
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:45:26.065839+00:00
-- url     : https://prove2.me/submissions/1b3a5d2c-1e36-4404-8625-d60e8a80b586

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeB
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeC
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_finOrd_56980a9f4222
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_no_prime_power_55c013f24499
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_exc_same_e360c4d3ec9d
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_exc_cross_9752624ee39d
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_coeff_zero_P_595d1fa987bb
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_exists_gen_1f25671aec83
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_exists_orbP_cf9d18d4d017
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_exists_pow_eq_89fec43dff7b
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_irreducible_P_8763ba5db034
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_le_natDegree_of_dvd_81216a4a9b35
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_mem_rootsBar_P_9cb9ba47d11d
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_orbQ_monic_0e02f754a39e


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.NZ
open Polynomial Formalism.CyclotomicNorms Formalism.CyclotomicNorms.CycleTypeFiniteOrder
variable {g : ℕ} [hg : Fact g.Prime]
namespace Formalism.BasicNotions.Examples₂.NZ
theorem _root_.solution (N p q0 : ℕ) (hp : p.Prime) (h1 : N < 2 * p) (h2 : p + 3 ≤ N) (hq0 : q0.Prime)
    (hq2 : q0 ≠ 2) (h2g : 2 ∣ g - 1) (hqg : q0 ∣ g - 1) :
    ∃ fA fB q : (ZMod g)[X], LabelOK N fA ∧ LabelOK N fB ∧
      (∀ r : (ZMod g)[X], r ∣ fA → r.natDegree ≠ 0 → N ≤ r.natDegree) ∧
      Irreducible q ∧ q ∣ fB ∧ q.natDegree = p := by
  have hN : 1 ≤ N := by omega
  set s := N - p with hs
  have hs1 : 1 ≤ s := by omega
  have hp1 : 1 ≤ p := hp.one_lt.le
  obtain ⟨uN, huN⟩ := exists_gen (g := g) N hN
  obtain ⟨up, hup⟩ := exists_gen (g := g) p hp1
  obtain ⟨us, hus⟩ := exists_gen (g := g) s hs1
  obtain ⟨PN, hPN, dN, mN⟩ := exists_orbP hN uN huN
  obtain ⟨Pp, hPp, dp, mp⟩ := exists_orbP hp1 up hup
  obtain ⟨Ps, hPs, ds, ms⟩ := exists_orbP hs1 us hus
  have iN := irreducible_P hN uN huN hPN dN
  have ip := irreducible_P hp1 up hup hPp dp
  have is := irreducible_P hs1 us hus hPs ds
  have one_fin : IsOfFinOrder (1 : Fbar g) := IsOfFinOrder.one
  have hcop : Nat.Coprime p s := (Nat.Prime.coprime_iff_not_dvd hp).mpr
    (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))
  have memB : ∀ y, y ∈ rootsBar (Pp * Ps) ↔ y ∈ rootsBar Pp ∨ y ∈ rootsBar Ps := fun y => by
    unfold rootsBar
    rw [Polynomial.map_mul, roots_mul (mul_ne_zero (by rw [hPp]; exact (orbQ_monic up).ne_zero)
      (by rw [hPs]; exact (orbQ_monic us).ne_zero)), Multiset.mem_add]
  refine ⟨PN, Pp * Ps, Pp, ⟨mN, dN, coeff_zero_P uN hPN, iN.squarefree, ?_, ?_⟩,
    ⟨mp.mul ms, by rw [mp.natDegree_mul ms, dp, ds]; omega, ?_, ?_, ?_, ?_⟩,
    fun r hr hr0 => le_natDegree_of_dvd hN uN huN hPN hr hr0, ip, Dvd.intro _ rfl, dp⟩
  · intro ℓ hℓ hBB x hx y hy hxy
    obtain ⟨i, hi, rfl⟩ := (mem_rootsBar_P uN hPN).mp hx
    obtain ⟨j, hj, rfl⟩ := (mem_rootsBar_P uN hPN).mp hy
    obtain ⟨c, hc⟩ := exists_pow_eq hℓ _ _ (finOrd hN uN huN i) (finOrd hN uN huN j) hxy
    by_contra hne
    exact hBB (Or.inr ⟨N, hN, le_rfl, exc_same hN uN huN hℓ hi hj (fun e => hne (by rw [e])) hc⟩)
  · intro ℓ hℓ x hx hxy
    obtain ⟨i, hi, rfl⟩ := (mem_rootsBar_P uN hPN).mp hx
    obtain ⟨c, hc⟩ := exists_pow_eq hℓ _ _ (finOrd hN uN huN i) one_fin hxy
    exact no_prime_power hN uN huN hℓ hq0 hq2 h2g hqg i c (by rw [hc, one_pow])
  · rw [mul_coeff_zero]; exact mul_ne_zero (coeff_zero_P up hPp) (coeff_zero_P us hPs)
  · refine squarefree_mul_iff.mpr ⟨ip.isRelPrime_iff_not_dvd.mpr fun hdv => ?_, ip.squarefree, is.squarefree⟩
    have := natDegree_le_of_dvd hdv ms.ne_zero
    omega
  · intro ℓ hℓ hBB x hx y hy hxy
    have hBp : ¬ Exc g p ℓ := fun h => hBB (Or.inr ⟨p, hp1, by omega, h⟩)
    have hBs : ¬ Exc g s ℓ := fun h => hBB (Or.inr ⟨s, hs1, by omega, h⟩)
    rcases (memB x).mp hx with hx | hx <;> rcases (memB y).mp hy with hy | hy
    · obtain ⟨i, hi, rfl⟩ := (mem_rootsBar_P up hPp).mp hx
      obtain ⟨j, hj, rfl⟩ := (mem_rootsBar_P up hPp).mp hy
      obtain ⟨c, hc⟩ := exists_pow_eq hℓ _ _ (finOrd hp1 up hup i) (finOrd hp1 up hup j) hxy
      by_contra hne
      exact hBp (exc_same hp1 up hup hℓ hi hj (fun e => hne (by rw [e])) hc)
    · obtain ⟨i, hi, rfl⟩ := (mem_rootsBar_P up hPp).mp hx
      obtain ⟨j, hj, rfl⟩ := (mem_rootsBar_P us hPs).mp hy
      obtain ⟨c, hc⟩ := exists_pow_eq hℓ _ _ (finOrd hp1 up hup i) (finOrd hs1 us hus j) hxy
      exact (hBp (exc_cross hℓ hp.two_le hs1 hcop up us hup hus i j c hc)).elim
    · obtain ⟨i, hi, rfl⟩ := (mem_rootsBar_P us hPs).mp hx
      obtain ⟨j, hj, rfl⟩ := (mem_rootsBar_P up hPp).mp hy
      obtain ⟨c, hc⟩ := exists_pow_eq hℓ _ _ (finOrd hs1 us hus i) (finOrd hp1 up hup j) hxy
      exact (hBp (exc_cross hℓ hp.two_le hs1 hcop up us hup hus j i c hc.symm)).elim
    · obtain ⟨i, hi, rfl⟩ := (mem_rootsBar_P us hPs).mp hx
      obtain ⟨j, hj, rfl⟩ := (mem_rootsBar_P us hPs).mp hy
      obtain ⟨c, hc⟩ := exists_pow_eq hℓ _ _ (finOrd hs1 us hus i) (finOrd hs1 us hus j) hxy
      by_contra hne
      exact hBs (exc_same hs1 us hus hℓ hi hj (fun e => hne (by rw [e])) hc)
  · intro ℓ hℓ x hx hxy
    rcases (memB x).mp hx with hx | hx
    · obtain ⟨i, hi, rfl⟩ := (mem_rootsBar_P up hPp).mp hx
      obtain ⟨c, hc⟩ := exists_pow_eq hℓ _ _ (finOrd hp1 up hup i) one_fin hxy
      exact no_prime_power hp1 up hup hℓ hq0 hq2 h2g hqg i c (by rw [hc, one_pow])
    · obtain ⟨i, hi, rfl⟩ := (mem_rootsBar_P us hPs).mp hx
      obtain ⟨c, hc⟩ := exists_pow_eq hℓ _ _ (finOrd hs1 us hus i) one_fin hxy
      exact no_prime_power hs1 us hus hℓ hq0 hq2 h2g hqg i c (by rw [hc, one_pow])
end Formalism.BasicNotions.Examples₂.NZ
