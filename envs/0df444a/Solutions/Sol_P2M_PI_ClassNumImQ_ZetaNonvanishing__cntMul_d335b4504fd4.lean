-- Prove2me | solution 1 for P2M_PI_ClassNumImQ_ZetaNonvanishing__cntMul_d335b4504fd4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:14:45.224598+00:00
-- url     : https://prove2.me/submissions/ed486880-4a31-4a66-8125-bf533ea68744

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ClassNumImQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticDedekindZeta_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticDedekindZeta_SpanNatCastSupEqTop
import Theorems.Thm_P2M_RH_P2M_PI_ClassNumImQ_ZetaNonvanishing__cnt_one_f98a1623b55b_697d2cc9c3d8fc66
import Theorems.Thm_P2M_PI_ClassNumImQ_ZetaNonvanishing__le_of_mul_eq_4de6eaa66ab0
import Theorems.Thm_P2M_PI_ClassNumImQ_ZetaNonvanishing__sup_parts_24c8b37f94af

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open PI PI.ClassNumImQ PI.ClassNumImQ.ZetaNonvanishing₂
variable {K : Type} [Field K] [NumberField K]
namespace PI.ClassNumImQ.ZetaNonvanishing₂
theorem _root_.solution : CntMul := by
  intro K _ _ m n hmn
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [Nat.coprime_zero_left] at hmn
    subst hmn
    simp [cnt_one]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Nat.coprime_zero_right] at hmn
    subst hmn
    simp [cnt_one]
  let Φ : {I : Ideal (𝓞 K) // Ideal.absNorm I = m} × {J : Ideal (𝓞 K) // Ideal.absNorm J = n} →
      {A : Ideal (𝓞 K) // Ideal.absNorm A = m * n} :=
    fun x => ⟨x.1.1 * x.2.1, by rw [map_mul, x.1.2, x.2.2]⟩
  have hΦ : Function.Bijective Φ := by
    constructor
    · rintro ⟨⟨I, hI⟩, ⟨J, hJ⟩⟩ ⟨⟨I', hI'⟩, ⟨J', hJ'⟩⟩ h
      have h' : I * J = I' * J' := congrArg Subtype.val h
      have hII : I = I' :=
        le_antisymm (le_of_mul_eq hmn hI' hJ h'.symm) (le_of_mul_eq hmn hI hJ' h')
      subst hII
      have hI0 : I ≠ 0 := by
        rw [Ideal.zero_eq_bot, ne_eq, ← Ideal.absNorm_eq_zero_iff, hI]
        omega
      have hJJ : J = J' := mul_left_cancel₀ hI0 h'
      subst hJJ
      rfl
    · rintro ⟨A, hA⟩
      obtain ⟨hprod, hI, hJ⟩ := sup_parts hmn hm hn hA
      exact ⟨⟨⟨_, hI⟩, ⟨_, hJ⟩⟩, Subtype.ext hprod⟩
  unfold cnt
  rw [← Nat.card_prod]
  exact (Nat.card_congr (Equiv.ofBijective Φ hΦ)).symm
end PI.ClassNumImQ.ZetaNonvanishing₂
