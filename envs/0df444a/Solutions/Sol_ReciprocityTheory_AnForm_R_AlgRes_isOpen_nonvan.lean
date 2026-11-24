-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.AlgRes.isOpen_nonvan
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:22:33.428891+00:00
-- url     : https://prove2.me/submissions/bbd6cc38-7ec6-4077-8550-92bdb4f15d02

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ExistsAtlas
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_SNCstep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial ReciprocityTheory.AnForm.M
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace ReciprocityTheory.AnForm.R
namespace AlgRes
theorem _root_.solution {P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {e : ℕ}
    (R : AlgRes ι P D e) (i : Fin R.n) (g : MvPolynomial (Fin (R.amb i)) ℂ) :
    IsOpen {y | y ∈ R.src i ∧ eval (R.coord i y) g ≠ 0} := by
  have hc : Continuous fun y : R.src i => R.coord i y := (R.isEmbedding i).continuous
  have ho : IsOpen ((fun y : R.src i => R.coord i y) ⁻¹' {v | eval v g ≠ 0}) :=
    (isOpen_ne_fun (MvPolynomial.continuous_eval g) continuous_const).preimage hc
  have h2 := (R.isOpen_alt_bis i).isOpenMap_subtype_val _ ho
  convert h2 using 1
  ext y
  simp [and_comm]
end AlgRes
end ReciprocityTheory.AnForm.R
