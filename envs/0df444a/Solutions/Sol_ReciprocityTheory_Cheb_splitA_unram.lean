-- Prove2me | solution 1 for ReciprocityTheory.Cheb.splitA_unram
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:58:14.256169+00:00
-- url     : https://prove2.me/submissions/1b2538a9-55e8-4af2-8e27-30c789925866

import Definitions.Def_ReciprocityTheory_Chebotarev_SplitDef
import Definitions.Def_ReciprocityTheory_Chebotarev_SplitA
import Theorems.Thm_ReciprocityTheory_Cheb_liesOver_of_under_eq
import Theorems.Thm_ReciprocityTheory_Cheb_norm_coprime_of_not_dvd_under
import Theorems.Thm_ReciprocityTheory_Cheb_inertia_trivial_cyclotomic_coprime

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
    (P : Prm (CyclotomicField l E)) (hP : under P = q) (hl : ¬ l ∣ Nrm q) :
    P.asIdeal.ramificationIdx (𝓞 E) = 1 := by
  have hlp : l.Prime := Fact.out
  have : NeZero l := ⟨hlp.ne_zero⟩
  have : IsGalois E (CyclotomicField l E) := IsCyclotomicExtension.isGalois {l} E (CyclotomicField l E)
  have := liesOver_of_under_eq P q hP
  have : q.asIdeal.IsMaximal := q.isMaximal
  have : Finite q.asIdeal.ResidueField :=
    Finite.of_surjective _ q.asIdeal.bijective_algebraMap_quotient_residueField.surjective
  have hcP := norm_coprime_of_not_dvd_under E l q P hP hl
  have hbot : P.asIdeal.inertia Gal(CyclotomicField l E/E) = ⊥ :=
    (Subgroup.eq_bot_iff_forall _).mpr fun g hg => inertia_trivial_cyclotomic_coprime E l P hcP g hg
  rw [← Ideal.ramificationIdxIn_eq_ramificationIdx q.asIdeal P.asIdeal Gal(CyclotomicField l E/E),
    ← Ideal.card_inertia_eq_ramificationIdxIn (G := Gal(CyclotomicField l E/E)) q.asIdeal P.asIdeal,
    hbot, Subgroup.card_bot]
end ReciprocityTheory.Cheb
