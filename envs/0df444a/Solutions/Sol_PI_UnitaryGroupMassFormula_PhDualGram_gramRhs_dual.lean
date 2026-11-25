-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.PhDualGram.gramRhs_dual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:48:08.190975+00:00
-- url     : https://prove2.me/submissions/14e50b0a-55cd-49a8-ad40-1cd50a908c6c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DualGramSubstitution_HasSubstRen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DualGramSubstitution_BeMulByZero
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhDualGram_mulBy_one
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhDualGram_be_mulBy_zero
import Theorems.Thm_PI_FglPhSplit_Wk_be_mulBy_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.PhDualGram
open PI.FglGram MvPowerSeries
variable {p : ℕ} [Fact p.Prime] {l ex ph : PowerSeries ℂ_[p]}
namespace PI.UnitaryGroupMassFormula.PhDualGram
theorem _root_.solution (hex0 : PowerSeries.constantCoeff ex = 0)
    (hph0 : PowerSeries.constantCoeff ph = 0) (hl0 : PowerSeries.constantCoeff l = 0)
    (hinvl : PowerSeries.subst l ex = PowerSeries.X) {κ ι : Type} [Fintype κ] [Fintype ι]
    (b b' : ι → κ → ℂ_[p] × ℂ_[p]) (hI : DualIso b b') {n : ℕ} (E : ι ⊕ ι ≃ Fin n)
    (hE : ∀ e e', E (Sum.inl e) < E (Sum.inr e')) :
    GramRhs l ex ph (fun j => Sum.elim b b' (E.symm j)) =
      ∑ e, be l ex ph (Xv (E (Sum.inl e))) (Xv (E (Sum.inr e))) := by
  obtain ⟨h1, h2, h3⟩ := hI
  have hdiag : ∀ x : ι ⊕ ι, hP (Sum.elim b b' x) (Sum.elim b b' x) = 0 := by
    rintro (e | e)
    exacts [h1 e e, h2 e e]
  have hXv : ∀ j : Fin n, constantCoeff (Xv j : MvPowerSeries (Fin n) ℂ_[p]) = 0 :=
    fun j => constantCoeff_X j
  have bz : ∀ (x : MvPowerSeries (Fin n) ℂ_[p]) (j : Fin n), be l ex ph (mulBy l ex 0 x) (Xv j) = 0 :=
    fun x j => be_mulBy_zero hex0 hph0 hl0 hinvl x (hXv j)
  have hE' : ∀ e e', ¬ E (Sum.inr e) < E (Sum.inl e') := fun e e' h => lt_asymm h (hE e' e)
  have hmix : ∀ e e', be l ex ph (mulBy l ex (hP (b e) (b' e')).1 (Xv (E (Sum.inl e))))
      (Xv (E (Sum.inr e'))) = if e = e' then be l ex ph (Xv (E (Sum.inl e))) (Xv (E (Sum.inr e'))) else 0 := by
    intro e e'
    rw [h3]
    split_ifs
    · rw [Prod.fst_one, mulBy_one hl0 hinvl (hXv _)]
    · rw [Prod.fst_zero, bz]
  unfold GramRhs
  rw [Finset.sum_eq_zero (fun j _ => by rw [hdiag, Prod.fst_zero, map_zero, zero_mul]), zero_add]
  simp only [Finset.sum_filter]
  rw [← E.sum_comp]
  refine (Finset.sum_congr rfl fun x _ => by rw [← E.sum_comp]).trans ?_
  simp only [Equiv.symm_apply_apply, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, h1, h2,
    Prod.fst_zero, bz, ite_self, Finset.sum_const_zero, hE, hE', if_true, if_false, hmix, zero_add,
    add_zero, Finset.sum_ite_eq]
  simp
end PI.UnitaryGroupMassFormula.PhDualGram
