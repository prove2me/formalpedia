-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L3.isTotPosDef_of_ortho
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:25:40.753088+00:00
-- url     : https://prove2.me/submissions/95432a1d-8744-426f-a3e4-80f828612da4

import Definitions.Def_Formalism_PeriodIntegrals_HermitianGenusExtension_SemilocalHermitianLattices_MassSt
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MassBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Definitions.Def_Formalism_PeriodIntegrals_HermitianGenusExtension_SemilocalHermitianLattices_FiniteDimensionalOfOrtho
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_StandardSymmetricSums_form_sum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_StandardSymmetricSums_exists_coord
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField Module
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L3
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
open StandardSymmetricSums
namespace ReciprocityTheory.ChartRestriction.L3
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hs : h.IsSymm) {L : Submodule (𝓞 K) V} {n : ℕ} (hL : Formalism.HermitianLatticesTheory.IsOrthoLattice h L n) :
    IsTotPosDef h := by
  obtain ⟨e, hli, hsp, -, he⟩ := hL
  intro x hx φ
  obtain ⟨c, rfl⟩ := exists_coord hsp x
  rw [form_sum he, map_sum, Complex.re_sum]
  have hc : ∃ i, c i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hx (by simp [hcon])
  obtain ⟨i, hi⟩ := hc
  have hterm : ∀ j, (φ (star (c j) * c j)).re = Complex.normSq (φ (c j)) := by
    intro j
    rw [map_mul, hK.2.1, Complex.normSq_eq_conj_mul_self.symm, Complex.ofReal_re]
  simp only [hterm]
  refine Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _) ⟨i, Finset.mem_univ _, ?_⟩
  exact Complex.normSq_pos.2 (by simpa using hi)
end ReciprocityTheory.ChartRestriction.L3
