-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassFin.posDefOfDefiniteSignature_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:58:53.489231+00:00
-- url     : https://prove2.me/submissions/211cb3bf-7625-4c10-bbb0-c5fce9f25ff2

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_ClassFiniteOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_PosDefOfDefiniteSignatureHolds
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassFin_Jpq_zero
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassFin_cT_conj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped ComplexOrder
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassFin
open PI.UJClassFin
namespace PI.UnitaryGroupMassFormula.UJClassFin
theorem _root_.solution : SigPos := by
  intro M A h
  unfold HasSignature at h
  obtain ⟨e, P, hP⟩ := h
  rw [cT_conj, Jpq_zero] at hP
  generalize hBdef : reindex e e A = B at hP
  obtain ⟨Q, hQ⟩ : ∃ Q : Matrix (Fin M ⊕ Fin 0) (Fin M ⊕ Fin 0) ℂ,
      Q = ((P⁻¹ : GL (Fin M ⊕ Fin 0) ℂ) : Matrix (Fin M ⊕ Fin 0) (Fin M ⊕ Fin 0) ℂ) := ⟨_, rfl⟩
  have hPQ : (P : Matrix (Fin M ⊕ Fin 0) (Fin M ⊕ Fin 0) ℂ) * Q = 1 := by
    rw [hQ]
    exact Units.mul_inv P
  have hinj : Function.Injective Q.mulVec := by
    intro x y hxy
    have h2 := congrArg (fun v => (P : Matrix (Fin M ⊕ Fin 0) (Fin M ⊕ Fin 0) ℂ) *ᵥ v) hxy
    simpa [Matrix.mulVec_mulVec, hPQ] using h2
  have hBeq : B = Qᴴ * 1 * Q := by
    calc B = ((P : Matrix (Fin M ⊕ Fin 0) (Fin M ⊕ Fin 0) ℂ) * Q)ᴴ * B
          * ((P : Matrix (Fin M ⊕ Fin 0) (Fin M ⊕ Fin 0) ℂ) * Q) := by
          rw [hPQ]; simp
      _ = Qᴴ * ((P : Matrix (Fin M ⊕ Fin 0) (Fin M ⊕ Fin 0) ℂ)ᴴ * B
          * (P : Matrix (Fin M ⊕ Fin 0) (Fin M ⊕ Fin 0) ℂ)) * Q := by
          rw [Matrix.conjTranspose_mul]
          simp only [Matrix.mul_assoc]
      _ = Qᴴ * 1 * Q := by rw [hP]
  have hBpos : B.PosDef := by
    rw [hBeq]
    exact Matrix.PosDef.one.conjTranspose_mul_mul_same hinj
  have hA : A = B.submatrix e e := by
    rw [← hBdef]
    ext i j
    simp
  rw [hA]
  exact hBpos.submatrix e.injective
end PI.UnitaryGroupMassFormula.UJClassFin
