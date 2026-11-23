-- Prove2me | solution 1 for P2M_Formalism_DoubleCosetMeasures_P_LemmaU_suppJ__bdf06674c24b
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:06:59.200398+00:00
-- url     : https://prove2.me/submissions/867b31f4-a913-4a3f-84e2-f0f2d604caf5

import Definitions.Def_Formalism_DoubleCosetMeasures_StatementZ
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LemmaU
import Theorems.Thm_P2M_Formalism_DoubleCosetMeasures_P_LemmaU_toRows__mul_3f124dd9bb9d
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MeasureTheory Matrix ComplexConjugate
namespace Formalism.DoubleCosetMeasures.P.LemmaU
open Formalism.DoubleCosetMeasures
section
variable {F : Type} [Field F] {a t : ℕ}
private theorem phiU_eq_zero_of_not_mem_support {O : Subring F} {ϖ : F} {J' : Subgroup (GL (Fin a) F)}
    {ρ : J' →* ℂˣ} {x : Matrix (Fin a ⊕ Fin t) (Fin a) F}
    (h : ¬ ((∃ k : J', ((k : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) = toRows₁ x) ∧
      toRows₂ x ∈ Formalism.DoubleCosetMeasures.IIset O ϖ)) :
    Formalism.DoubleCosetMeasures.phiU O ϖ J' ρ x = 0 := by
  simp only [Formalism.DoubleCosetMeasures.phiU]
  rw [dif_neg h]
end
end Formalism.DoubleCosetMeasures.P.LemmaU
namespace Formalism.DoubleCosetMeasures.P
end Formalism.DoubleCosetMeasures.P
end

set_option autoImplicit false
open MeasureTheory Matrix ComplexConjugate
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P Formalism.DoubleCosetMeasures.P.LemmaU
open Formalism.DoubleCosetMeasures
namespace Formalism.DoubleCosetMeasures.P.LemmaU
theorem _root_.solution : SuppJ := by
  intro F _ _ a t O ϖ J' ρ χ nrm ν g hg
  unfold Formalism.DoubleCosetMeasures.weilIP
  have hz : ∀ x : Matrix (Fin a ⊕ Fin t) (Fin a) F,
      Formalism.DoubleCosetMeasures.omegaS χ nrm g (Formalism.DoubleCosetMeasures.phiU (t := t) O ϖ J' ρ) x * conj (Formalism.DoubleCosetMeasures.phiU O ϖ J' ρ x) = 0 := by
    intro x
    by_cases hx : ∃ k : J', ((k : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) = toRows₁ x
    · obtain ⟨k, hk⟩ := hx
      have h0 : Formalism.DoubleCosetMeasures.phiU (t := t) O ϖ J' ρ (x * (g : Matrix (Fin a) (Fin a) F)) = 0 := by
        apply phiU_eq_zero_of_not_mem_support
        rintro ⟨⟨k', hk'⟩, -⟩
        apply hg
        have e : ((k : GL (Fin a) F) * g : GL (Fin a) F) = k' := by
          apply Units.ext
          rw [Units.val_mul, hk, hk', toRows₁_mul]
        have hgk : g = (k : GL (Fin a) F)⁻¹ * k' := by
          rw [← e, inv_mul_cancel_left]
        rw [hgk]
        exact J'.mul_mem (J'.inv_mem k.2) k'.2
      simp only [Formalism.DoubleCosetMeasures.omegaS, h0, mul_zero, zero_mul]
    · rw [phiU_eq_zero_of_not_mem_support (fun h => hx h.1)]
      simp
  simp only [hz, integral_zero]
end Formalism.DoubleCosetMeasures.P.LemmaU
