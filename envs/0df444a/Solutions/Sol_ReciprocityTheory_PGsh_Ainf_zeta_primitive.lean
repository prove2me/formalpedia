-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Ainf.zeta_primitive
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:04:23.435585+00:00
-- url     : https://prove2.me/submissions/4544a2f4-4ef5-4a64-b6e8-c1d733565419

import Definitions.Def_ReciprocityTheory_DualLattices_AinfTower
import Definitions.Def_ReciprocityTheory_DualLattices_HtLinStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Theorems.Thm_ReciprocityTheory_PGsh_Ainf_root_pow_one
import Theorems.Thm_ReciprocityTheory_PGsh_Ainf_root_pow
import Theorems.Thm_ReciprocityTheory_PGsh_Ainf_untilt_eps


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open WittVector Ideal
open ReciprocityTheory ReciprocityTheory.PGsh
open ReciprocityTheory.PGsh.Ainf
variable (p : ℕ) [hp : Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  {v : Valuation C NNReal} (O : Type) [CommRing O] [Algebra O C]
  [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O]
  (hv : v.Integers O) (ε : PreTilt O p)
  (hε : IsPrimitiveRoot (((frobeniusEquiv (PreTilt O p) p).symm ε).untilt) p)
include hv hε
namespace ReciprocityTheory.PGsh.Ainf
theorem _root_.solution (n : ℕ) : IsPrimitiveRoot (zetaV p O ε n) (p ^ (n + 1)) := by
  have hz1 : zetaV p O ε n ^ p ^ (n + 1) = 1 := by
    rw [zetaV, ← map_pow, ← map_pow, root_pow, fontaineTheta_teichmuller,
      untilt_eps p O hv ε hε]
  have hzn : zetaV p O ε n ^ p ^ n ≠ 1 := by
    rw [zetaV, ← map_pow, ← map_pow, root_pow_one, fontaineTheta_teichmuller]
    exact hε.ne_one hp.out.one_lt
  have hord : orderOf (zetaV p O ε n) ∣ p ^ (n + 1) := orderOf_dvd_of_pow_eq_one hz1
  obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow hp.out).1 hord
  have hjn : j = n + 1 := by
    by_contra hne
    have hle : j ≤ n := by omega
    apply hzn
    have : orderOf (zetaV p O ε n) ∣ p ^ n := by rw [hj']; exact pow_dvd_pow p hle
    exact orderOf_dvd_iff_pow_eq_one.1 this
  rw [← hjn, ← hj']
  exact IsPrimitiveRoot.orderOf _
end ReciprocityTheory.PGsh.Ainf
