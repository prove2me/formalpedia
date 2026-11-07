-- Prove2me | solution 1 for QEC.Coding.CSSGibbs.jointProbability_product
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:27:18.740184+00:00
-- url     : https://prove2.me/submissions/355ce2bd-4497-4e78-8a0c-22ce757917f4

import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Spectrum
import Definitions.Def_QEC_Semantics_Dynamics_Davies_Hamiltonian
import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Gibbs
import Theorems.Thm_QEC_Coding_CSSGibbs_mem_realizableSyndromes_iff
import Theorems.Thm_QEC_Coding_CSSGibbs_weight_joinSyndrome


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.CSSGibbs
open Classical PauliSymplectic StabilizerCode Semantics Semantics.Davies Semantics.ThermalEncoding
open scoped BigOperators
variable {ι κP κQ : Type} [Fintype ι] [DecidableEq ι]
  [Fintype κP] [Fintype κQ] [DecidableEq κP] [DecidableEq κQ]
variable (P : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κP)
  (Q : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κQ)
  (horth : ∀ p q, wordPairing (parityCheckRow P p) (parityCheckRow Q q) = 0)
attribute [local instance] QEC.Coding.CSSGibbs._p2m_local_instance_28fb820634_14
attribute [local instance] QEC.Coding.CSSGibbs._p2m_local_instance_28fb820634_15
namespace QEC.Coding.CSSGibbs
theorem _root_.solution (β : ℝ) (u : LinearMap.range P) (v : LinearMap.range Q) :
    jointProbability P Q β (joinSyndrome u.val v.val) =
      rowProbability P (2 * β) u * rowProbability Q (2 * β) v := by
  have hs : joinSyndrome u.val v.val ∈ realizableSyndromes P Q :=
    (mem_realizableSyndromes_iff P Q _).mpr ⟨u.property, v.property⟩
  rw [jointProbability, if_pos hs, weight_joinSyndrome]
  push_cast
  rw [mul_add, Real.exp_add, rowProbability, rowProbability, div_mul_div_comm]
end QEC.Coding.CSSGibbs
