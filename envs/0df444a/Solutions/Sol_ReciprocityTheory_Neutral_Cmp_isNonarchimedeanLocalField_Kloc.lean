-- Prove2me | solution 1 for ReciprocityTheory.Neutral.Cmp.isNonarchimedeanLocalField_Kloc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:30:41.030649+00:00
-- url     : https://prove2.me/submissions/b7bee4ab-2a24-4934-a458-8a43d4a1268a

import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_MemRangeOfAevalRatEqZero
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_ModelA
import Theorems.Thm_ReciprocityTheory_Neutral_Cmp_valuation_lt_iff_Kloc
import Theorems.Thm_ReciprocityTheory_Neutral_Cmp_norm_natCast_p_Kloc
import Theorems.Thm_ReciprocityTheory_Neutral_Cmp_finiteDimensional_Kloc


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.Neutral ReciprocityTheory.Neutral.Cmp
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain ValuativeRel
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {p : ℕ} [Fact p.Prime]
attribute [local instance] locRel
namespace ReciprocityTheory.Neutral.Cmp
theorem _root_.solution (ι : Ω →+* PadicAlgCl p) : IsNonarchimedeanLocalField (Kloc F ι) := by
  have : FiniteDimensional ℚ_[p] (Kloc F ι) := finiteDimensional_Kloc ι
  have : ProperSpace (Kloc F ι) := FiniteDimensional.proper ℚ_[p] (Kloc F ι)
  set q : Kloc F ι := ((p : ℕ) : Kloc F ι) with hq
  have hq1 : ‖(q : PadicAlgCl p)‖ < 1 := norm_natCast_p_Kloc ι
  have hq0 : q ≠ 0 := by
    rw [hq]; exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hqn : 0 < ‖(q : PadicAlgCl p)‖ := by
    rw [norm_pos_iff]; exact_mod_cast hq0
  have hnt : ValuativeRel.IsNontrivial (Kloc F ι) := by
    refine ⟨⟨valuation (Kloc F ι) q, ?_, ?_⟩⟩
    · simpa using hq0
    · intro h
      have := (valuation_lt_iff_Kloc ι q 1).2 (by simpa using hq1)
      rw [h, map_one] at this
      exact lt_irrefl _ this
  have hvt : IsValuativeTopology (Kloc F ι) := by
    constructor
    intro s x
    rw [Metric.mem_nhds_iff]
    constructor
    · rintro ⟨ε, hε, hs⟩
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hq1
      have hqn0 : q ^ n ≠ 0 := pow_ne_zero _ hq0
      refine ⟨Units.mk0 (valuation (Kloc F ι) (q ^ n)) (by simpa using hqn0), ?_⟩
      rintro _ ⟨z, hz, rfl⟩
      apply hs
      rw [Set.mem_ofPred_eq, Units.val_mk0, valuation_lt_iff_Kloc] at hz
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
      calc ‖z‖ = ‖(z : PadicAlgCl p)‖ := rfl
        _ < ‖((q ^ n : Kloc F ι) : PadicAlgCl p)‖ := hz
        _ = ‖(q : PadicAlgCl p)‖ ^ n := by simp
        _ < ε := hn
    · rintro ⟨γ, hγ⟩
      obtain ⟨y, hy⟩ := valuation_surjective (γ : ValueGroupWithZero (Kloc F ι))
      have hy0 : y ≠ 0 := by
        rintro rfl; simp at hy; exact γ.ne_zero hy.symm
      refine ⟨‖(y : PadicAlgCl p)‖, by rw [gt_iff_lt, norm_pos_iff]; exact_mod_cast hy0, fun w hw => hγ ?_⟩
      refine ⟨w - x, ?_, by simp⟩
      rw [Set.mem_ofPred_eq, ← hy, valuation_lt_iff_Kloc]
      rw [Metric.mem_ball, dist_eq_norm] at hw
      exact hw
  exact { toIsValuativeTopology := hvt, toLocallyCompactSpace := inferInstance, toIsNontrivial := hnt }
end ReciprocityTheory.Neutral.Cmp
