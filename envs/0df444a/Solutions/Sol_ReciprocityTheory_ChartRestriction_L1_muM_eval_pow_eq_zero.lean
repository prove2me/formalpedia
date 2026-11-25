-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.muM_eval_pow_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:38:44.856044+00:00
-- url     : https://prove2.me/submissions/7ab75432-1a24-43ed-88e4-ce5c7e4a54ee

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_KurDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_MuMEvalPowEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open Formalism.L2.Th1.CM Polynomial
variable (l : ℕ) [Fact l.Prime]
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution {K : Type*} [Field K] [CharZero K] (n : ℕ) (hn : 0 < n) (hln : ¬ l ∣ n)
    (g : K) (hg : g ^ n = 1) (p : ℤ[X]) (hp : p.eval₂ (Int.castRingHom K) g = 0) :
    p.eval₂ (Int.castRingHom K) (g ^ l) = 0 := by
  rw [← algebraMap_int_eq, ← aeval_def] at hp ⊢
  have hd : orderOf g ∣ n := orderOf_dvd_of_pow_eq_one hg
  have hd0 : 0 < orderOf g := Nat.pos_of_dvd_of_pos hd hn
  have hprim : IsPrimitiveRoot g (orderOf g) := IsPrimitiveRoot.orderOf g
  have hcop : Nat.Coprime l (orderOf g) :=
    ((Fact.out : l.Prime).coprime_iff_not_dvd).2 fun h => hln (h.trans hd)
  have hdvd : minpoly ℤ g ∣ p := minpoly.isIntegrallyClosed_dvd (hprim.isIntegral hd0) hp
  rw [hprim.minpoly_eq_pow_coprime hcop] at hdvd
  exact aeval_eq_zero_of_dvd_aeval_eq_zero hdvd (minpoly.aeval ℤ (g ^ l))
end ReciprocityTheory.ChartRestriction.L1
