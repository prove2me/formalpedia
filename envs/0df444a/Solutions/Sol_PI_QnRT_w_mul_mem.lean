-- Prove2me | solution 1 for PI.QnRT.w_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:43:22.263728+00:00
-- url     : https://prove2.me/submissions/40b37ded-00c5-4a31-92b1-4ea353704d31

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusConjugationRule_WColOther
import Theorems.Thm_PI_QnRT_w_uh
import Theorems.Thm_PI_QnRT_w_fix
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
namespace PI.QnRT
variable {k r : ℕ}
private lemma mul_mem_uh {g h : Mx k r} (hg : g ∈ UH (Hpk k r)) (hh : h ∈ UH (Hpk k r)) :
    g * h ∈ UH (Hpk k r) := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have hh' : hᴴ * Hpk k r * h = Hpk k r := hh
  show (g * h)ᴴ * Hpk k r * (g * h) = Hpk k r
  rw [Matrix.conjTranspose_mul]
  calc hᴴ * gᴴ * Hpk k r * (g * h) = hᴴ * (gᴴ * Hpk k r * g) * h := by
        simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [hg', hh']
end PI.QnRT
end
end

set_option autoImplicit false
open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
open PI PI.QnRT
variable {k r : ℕ}
namespace PI.QnRT
theorem _root_.solution (l : Fin r) (a : ℂ) (ha : a ≠ 0) (g₁ : Mx k r) (hg : g₁ ∈ Glev k r l.succ) :
    w1 k r l a * g₁ ∈ Glev k r l.castSucc := by
  have hl := l.isLt
  simp only [Glev, Set.mem_setOf_eq] at hg ⊢
  obtain ⟨hU, hfix⟩ := hg
  refine ⟨mul_mem_uh (w_uh l a ha) hU, fun b hb => ?_⟩
  have hbl := b.isLt
  simp only [Fin.coe_castSucc] at hb
  have hfb := hfix b (by simp; omega)
  have h1 : eI k r b ≠ eI k r l := fun h => by
    have h' := congrArg Fin.val h
    simp only [eI] at h'
    omega
  have h2 : eI k r b ≠ esI k r l := fun h => by
    have h' := congrArg Fin.val h
    simp only [eI, esI] at h'
    omega
  have h3 : esI k r b ≠ eI k r l := fun h => by
    have h' := congrArg Fin.val h
    simp only [eI, esI] at h'
    omega
  have h4 : esI k r b ≠ esI k r l := fun h => by
    have h' := congrArg Fin.val h
    simp only [esI] at h'
    omega
  constructor
  · rw [← Matrix.mulVec_mulVec, hfb.1, w_fix l a _ h1 h2]
  · rw [← Matrix.mulVec_mulVec, hfb.2, w_fix l a _ h3 h4]
end PI.QnRT
