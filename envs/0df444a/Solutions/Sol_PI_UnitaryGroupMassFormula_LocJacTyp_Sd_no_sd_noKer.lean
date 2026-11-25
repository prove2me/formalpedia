-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LocJacTyp.Sd.no_sd_noKer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:32:32.16125+00:00
-- url     : https://prove2.me/submissions/799b601d-25c7-4aea-9778-e643c7105e74

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_ChiZeroRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_ComponentsOfD1EqZero
import Theorems.Thm_P2M_PI_UnitaryGroupMassFormula_LocJacTyp_Sd_finrank_pos__e568ad97088d
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_Sd_components_of_D1_eq_zero
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_Sd_bas_mem
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_Sd_coe_ObS
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_Sd_isCompact_obox
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_Sd_sd_test
import Theorems.Thm_PI_VolStabSW_locallyCompact_Fv
import Theorems.Thm_PI_VolStabSW_secondCountable_Fv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LocJacTyp PI.UnitaryGroupMassFormula.LocJacTyp.Sd
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain Topology Filter PI.LocJacTyp
open PI.VolStabSW.SdUniqW
open scoped TensorProduct
attribute [local instance] PI.VolStabSW.secondCountable_Fv PI.VolStabSW.locallyCompact_Fv finDim
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) (ψ : AddChar (AF F) ℂ)
variable [SecondCountableTopology (Fv F v ⊗[F] E)]
namespace PI.UnitaryGroupMassFormula.LocJacTyp.Sd
theorem _root_.solution (ι : Type) [Fintype ι] [Nonempty ι] (h : ¬ OpenKer v ψ) :
    ¬ ∃ μ : Measure (ι → Fv F v ⊗[F] E), SelfDual μ (chi (E := E) v ψ ι) := by
  classical
  rintro ⟨μ, hμ⟩
  have := hμ.1
  have hD : Dbox (E := E) v ψ ι = {0} := by
    ext y
    simp only [Dbox, components_of_D1_eq_zero v ψ h, Set.mem_pi, Set.mem_univ, Set.mem_singleton_iff,
      true_implies]
    exact ⟨fun hy => funext hy, fun hy i => by rw [hy]; rfl⟩
  have h1 := sd_test v ψ ι μ hμ (by rw [hD]; exact measurableSet_singleton 0)
    (by rw [hD]; exact measure_singleton_lt_top)
  rw [hD] at h1
  have h0 : μ {0} ≠ 0 := by
    intro h0
    simp [Measure.real, h0] at h1
  obtain ⟨i0⟩ := ‹Nonempty ι›
  set j0 : Fin (Module.finrank F E) := ⟨0, finrank_pos'⟩
  set x1 : ι → Fv F v ⊗[F] E := Pi.single i0 (bas (E := E) v j0)
  have hx1 : x1 ≠ 0 := by
    intro hx
    have := congrFun hx i0
    simp [x1] at this
    exact (bas (E := E) v).ne_zero j0 this
  have hx1m : ∀ n : ℕ, n • x1 ∈ Obox (E := E) v ι := by
    intro n
    have hm : x1 ∈ ObS (E := E) v ι := by
      rw [← SetLike.mem_coe, coe_ObS]
      intro i _
      by_cases hi : i = i0
      · subst hi; simpa [x1] using bas_mem v j0
      · simpa [x1, hi] using oev_zero v
    have := (ObS (E := E) v ι).nsmul_mem hm n
    rwa [← SetLike.mem_coe, coe_ObS] at this
  have : CharZero (Fv F v) := charZero_of_injective_algebraMap (algebraMap F (Fv F v)).injective
  have hinj : ∀ n m : ℕ, n • x1 = m • x1 → n = m := by
    intro n m hnm
    rw [← Nat.cast_smul_eq_nsmul (Fv F v), ← Nat.cast_smul_eq_nsmul (Fv F v), ← sub_eq_zero,
      ← sub_smul, smul_eq_zero] at hnm
    rcases hnm with h' | h'
    · exact Nat.cast_injective (R := Fv F v) (sub_eq_zero.1 h')
    · exact absurd h' hx1
  have hpt : ∀ a : ι → Fv F v ⊗[F] E, μ {a} = μ {0} := by
    intro a
    have e : ({a} : Set (ι → Fv F v ⊗[F] E)) = (fun h => -a + h) ⁻¹' {0} := by
      ext y; simp [eq_comm]
    rw [e, measure_preimage_add]
  have hfin : μ (Obox (E := E) v ι) ≠ ⊤ := (isCompact_obox v ι).measure_lt_top.ne
  obtain ⟨N, hN⟩ := ENNReal.exists_nat_mul_gt h0 hfin
  have hS : μ (⋃ n ∈ Finset.range N, {n • x1}) = N * μ {0} := by
    rw [measure_biUnion_finset]
    · rw [Finset.sum_congr rfl (fun n _ => hpt (n • x1)), Finset.sum_const, Finset.card_range,
        nsmul_eq_mul]
    · intro n _ m _ hnm
      exact Set.disjoint_singleton.2 fun h' => hnm (hinj n m h')
    · intro n _; exact measurableSet_singleton _
  have hsub : (⋃ n ∈ Finset.range N, ({n • x1} : Set (ι → Fv F v ⊗[F] E))) ⊆ Obox (E := E) v ι := by
    intro y hy
    simp only [Set.mem_iUnion, Set.mem_singleton_iff] at hy
    obtain ⟨n, _, rfl⟩ := hy
    exact hx1m n
  have := measure_mono (μ := μ) hsub
  rw [hS] at this
  exact absurd (lt_of_lt_of_le hN this) (lt_irrefl _)
end PI.UnitaryGroupMassFormula.LocJacTyp.Sd
