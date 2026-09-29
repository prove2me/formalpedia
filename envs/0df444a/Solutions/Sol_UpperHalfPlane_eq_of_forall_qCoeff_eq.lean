-- Prove2me | solution 1 for UpperHalfPlane.eq_of_forall_qCoeff_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/335e7620-2dc9-5c6e-87f5-74e923b83810

import Mathlib.NumberTheory.ModularForms.QExpansion
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_UpperHalfPlane_eq_of_forall_qCoeff_eq

set_option autoImplicit false

noncomputable section

open Complex Function Filter
p2m_open "UpperHalfPlane~I"
open scoped Real MatrixGroups ModularForm Manifold Topology

open ModularForm ModularFormClass

namespace W2WsF

theorem hasSum_qCoeff {f : ℍ → ℂ} (hper : Periodic (f ∘ ofComplex) 1) (hhol : MDiff f)
    (hbdd : IsBoundedAtImInfty f) (τ : ℍ) :
    HasSum (fun m ↦ qCoeff f m • Periodic.qParam 1 τ ^ m) (f τ) :=
  hasSum_qExpansion one_pos hper hhol hbdd τ

end W2WsF

theorem solution {f g : UpperHalfPlane → ℂ} (hfper : Function.Periodic (f ∘ UpperHalfPlane.ofComplex) 1) (hfhol : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) f) (hfbdd : UpperHalfPlane.IsBoundedAtImInfty f) (hgper : Function.Periodic (g ∘ UpperHalfPlane.ofComplex) 1) (hghol : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) g) (hgbdd : UpperHalfPlane.IsBoundedAtImInfty g) (h : ∀ n : ℕ, ModularFormClass.qCoeff f n = ModularFormClass.qCoeff g n) : f = g := by
  funext τ
  have hf := W2WsF.hasSum_qCoeff hfper hfhol hfbdd τ
  have hg := W2WsF.hasSum_qCoeff hgper hghol hgbdd τ
  simp only [h] at hf
  exact hf.unique hg

end

end S_UpperHalfPlane_eq_of_forall_qCoeff_eq
end P2MW
export P2MW.S_UpperHalfPlane_eq_of_forall_qCoeff_eq (solution)
