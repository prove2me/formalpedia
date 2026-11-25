-- Prove2me | solution 1 for PIW.ClassFinD.diagGL_mem_KGL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:27:05.619109+00:00
-- url     : https://prove2.me/submissions/ff243e82-7c31-4637-9edc-ec69afcc5704

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdeleClassFiniteness_OhatCompact
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdeleClassFiniteness_BorelGL
import Theorems.Thm_PIW_ClassFinD_diagGL_val

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.ClassFinD
open NumberField IsDedekindDomain
namespace PIW.ClassFinD
theorem _root_.solution (F : Type) [Field F] [NumberField F] (n : ℕ) (e : Fin n → (FiniteAdeleRing (𝓞 F) F)ˣ)
    (h1 : ∀ i, (e i : FiniteAdeleRing (𝓞 F) F) ∈ Ohat F)
    (h2 : ∀ i, ((e i)⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ).val ∈ Ohat F) : diagGL n e ∈ KGL F n := by
  have hd : ∀ d : Fin n → FiniteAdeleRing (𝓞 F) F, (∀ i, d i ∈ Ohat F) →
      MatInt (Matrix.diagonal d) := by
    intro d hd i j
    rw [Matrix.diagonal_apply]
    split_ifs with hij
    · subst hij
      exact hd i
    · exact (Ohat F).zero_mem
  show MatInt (diagGL n e).val ∧ MatInt (diagGL n e)⁻¹.val
  constructor
  · rw [diagGL_val]
    exact hd _ h1
  · rw [← map_inv (diagGL (R := FiniteAdeleRing (𝓞 F) F) n), diagGL_val]
    exact hd _ fun i => h2 i
end PIW.ClassFinD
