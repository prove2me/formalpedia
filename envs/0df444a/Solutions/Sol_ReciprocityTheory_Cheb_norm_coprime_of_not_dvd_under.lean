-- Prove2me | solution 1 for ReciprocityTheory.Cheb.norm_coprime_of_not_dvd_under
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:43:10.685495+00:00
-- url     : https://prove2.me/submissions/90068ee9-734a-452c-8012-b09ba5ef34be

import Definitions.Def_ReciprocityTheory_Chebotarev_SplitDef
import Definitions.Def_ReciprocityTheory_Chebotarev_SplitA
import Theorems.Thm_ReciprocityTheory_Cheb_liesOver_of_under_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Filter Topology
open ReciprocityTheory ReciprocityTheory.Cheb
namespace ReciprocityTheory.Cheb
theorem _root_.solution (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime] (q : Prm E)
    (P : Prm (CyclotomicField l E)) (hP : under P = q) (hl : ¬ l ∣ Nrm q) : Nat.Coprime (Nrm P) l := by
  have hlp : l.Prime := Fact.out
  have := liesOver_of_under_eq P q hP
  have hN : Nrm q ^ P.asIdeal.inertiaDeg (𝓞 E) = Nrm P :=
    Ideal.absNorm_pow_inertiaDeg q.asIdeal P.asIdeal
  have hcq : Nat.Coprime (Nrm q) l := (Nat.coprime_comm).mp ((Nat.Prime.coprime_iff_not_dvd hlp).mpr hl)
  exact hN ▸ Nat.Coprime.pow_left _ hcq
end ReciprocityTheory.Cheb
