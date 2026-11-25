-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.uRepCompRed_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:26:07.482947+00:00
-- url     : https://prove2.me/submissions/fddd32be-53f9-4ffb-8f31-0a7fc70d1cc7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ContinuousRepresentations_DerivExistsAllPosStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_SingleMulJmComm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ContinuousRepresentations_URepCompRedOf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_KRep_actM_units
import Theorems.Thm_Formalism_REAL_maximal_compact_facts


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Filter Topology
open scoped InnerProductSpace
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.HW
theorem _root_.solution (hU : URepHomStatement) (hD : DerivExistsStatement)
    (hR : KRepRelStatement) (hC : CompRedStatement) : URepCompRedStatement := by
  intro n ε H _ _ _ σ hσ
  obtain ⟨τ, hτc, hτ⟩ := hU n ε H σ hσ
  obtain ⟨dτ, hd⟩ := hD n ε H τ hτc
  obtain ⟨hRel, hUnit⟩ := hR n ε (compactRepOfUnitaryDifferential ε H τ hτc dτ hd)
  obtain ⟨m, x, μ, h1, h2, h3, h4, h5, h6⟩ := hC n ε (compactRepOfUnitaryDifferential ε H τ hτc dτ hd)
  refine ⟨(compactRepOfUnitaryDifferential ε H τ hτc dτ hd).units, hRel, hUnit, ?_, m, x, μ, h1, h2, h3, ?_⟩
  · intro X hX v
    have hK : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ Kset ε := fun t =>
      (Formalism.REAL.maximal_compact_facts n ε).2.2.2.1 _ (Formalism.REAL.inK_smul_real ε hX t)
    have hγ : ∀ t : ℝ, toMK (cr2K ε (hK t)) = NormedSpace.exp ((t : ℂ) • X) := fun t => rfl
    have hder := hd X hX (fun t => cr2K ε (hK t)) hγ
    erw [KRep.actM_units (compactRepOfUnitaryDifferential ε H τ hτc dτ hd) X v]
    have hfun : (fun t : ℝ => (σ (NormedSpace.exp ((t : ℂ) • X))) v) =
        fun t : ℝ => (((τ (cr2K ε (hK t)) : unitary (H →L[ℂ] H)) : H →L[ℂ] H)) v := by
      funext t; rw [hτ, hγ]
    rw [hfun]
    have h2 := ((ContinuousLinearMap.apply ℂ H v).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hder
    exact h2
  · refine ⟨?_, ?_⟩
    · intro i g hg v hv
      have := h5 i (cr2K ε hg) v hv
      simp only [KRep.op, compactRepOfUnitaryDifferential] at this
      have e : σ g = ((τ (cr2K ε hg) : unitary (H →L[ℂ] H)) : H →L[ℂ] H) := by
        rw [hτ]; rfl
      rw [e]; exact this
    · intro i
      obtain ⟨T, φ, -, hop, hdτ, hw⟩ := h6 i
      refine ⟨T, φ, ?_, ?_, hw⟩
      · intro k v
        have e : σ (toMK k) = ((τ k : unitary (H →L[ℂ] H)) : H →L[ℂ] H) := (hτ k).symm
        rw [e]; exact hop k v
      · intro a b hab v
        have hc : Matrix.single a b (1 : ℂ) * Jm ε = Jm ε * Matrix.single a b 1 := by
          show Matrix.single a b (1 : ℂ) * Matrix.diagonal _ = Matrix.diagonal _ * Matrix.single a b 1
          ext i j
          rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.single_apply]
          by_cases h : a = i ∧ b = j
          · obtain ⟨rfl, rfl⟩ := h; simp [hab]
          · simp [h]
        exact hdτ _ hc v
end ReciprocityTheory.ChartRestriction.DS.HW
