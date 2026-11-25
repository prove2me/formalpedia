-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnimodLocStd.not_dvd_relIndex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:46:01.35852+00:00
-- url     : https://prove2.me/submissions/0bcde24b-00ba-419e-9e1f-a58a3cd53e93

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RelIdxNeZeroOfLeLeft

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
namespace PI.UnitaryGroupMassFormula.UnimodLocStd
theorem _root_.solution {A B : AddSubgroup V} {l n : ℕ} (hl : l.Prime) (hAB : A.relIndex B ≠ 0)
    (hn : ∀ y ∈ B, n • y ∈ A) (hln : ¬ l ∣ n) : ¬ l ∣ A.relIndex B := by
  intro hdvd
  haveI : Fact l.Prime := ⟨hl⟩
  haveI : Finite (B ⧸ A.addSubgroupOf B) :=
    Nat.finite_of_card_ne_zero (α := B ⧸ A.addSubgroupOf B) hAB
  have hcard : l ∣ Nat.card (B ⧸ A.addSubgroupOf B) := hdvd
  obtain ⟨q, hq⟩ : ∃ q : B ⧸ A.addSubgroupOf B, addOrderOf q = l := by
    exact exists_prime_addOrderOf_dvd_card' l hcard
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective q
  apply hln
  rw [← hq]
  apply addOrderOf_dvd_of_nsmul_eq_zero
  rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
  exact hn _ y.2
end PI.UnitaryGroupMassFormula.UnimodLocStd
