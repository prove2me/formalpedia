-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LatticeModel_mem_quotField_f112b4739b83
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:22:06.583088+00:00
-- url     : https://prove2.me/submissions/b0182be3-add0-4af6-a54e-e4ca043b85fa

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockModelA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockModelB
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeModel_dehom_mem_quotField_80f3aaaa24c0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeModel_algebraMap_C_06ff1ad36227


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory.Heights₂.Heights.LatticeModel
variable {K : Type} [Field K] [NumberField K] {m N : ℕ} {L : Submodule (𝓞 K) (Fin m → K)}
variable {φ : Fin (N + 1) → Fin m → K}
variable {r : ℕ} {L : Submodule (𝓞 K) (Fin (r + 1) → K)} {φ : Fin (N + 1) → Fin (r + 1) → K}
namespace GroundTheory.Heights₂.Heights.LatticeModel
theorem _root_.solution (hL : L.FG) (hφ : IsDualBasis L φ) (s : LatticeField K r) : s ∈ quotField φ := by
  have hpoly : ∀ p : MvPolynomial (Fin r) K, algebraMap _ (LatticeField K r) p ∈ quotField φ := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a =>
      have e : algebraMap (MvPolynomial (Fin r) K) (LatticeField K r) (C a) = dehom K r (latticeForm (Pi.single 0 a)) := by
        simp [dehom, latticeForm, Pi.single_apply, genericVal, algebraMap_C, Fin.sum_univ_succ]
      rw [e]
      exact dehom_mem_quotField hL hφ _
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | mul_X p j hp =>
      rw [map_mul]
      refine mul_mem hp ?_
      have e : algebraMap (MvPolynomial (Fin r) K) (LatticeField K r) (X j) = dehom K r (latticeForm (Pi.single j.succ 1)) := by
        simp [dehom, latticeForm, Pi.single_apply, genericVal]
      rw [e]
      exact dehom_mem_quotField hL hφ _
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial (Fin r) K) s
  exact div_mem (hpoly a) (hpoly b)
end GroundTheory.Heights₂.Heights.LatticeModel
